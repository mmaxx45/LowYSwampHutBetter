package project;

import com.seedfinding.mccore.rand.ChunkRand;
import com.seedfinding.mccore.util.pos.CPos;
import com.seedfinding.mccore.version.MCVersion;
import com.seedfinding.mcfeature.structure.SwampHut;
import net.minecraft.block.Blocks;
import nl.jellejurre.seedchecker.SeedChecker;
import nl.jellejurre.seedchecker.SeedCheckerDimension;
import nl.jellejurre.seedchecker.TargetState;
import nl.kallestruik.noisesampler.minecraft.NoiseColumnSampler;
import nl.kallestruik.noisesampler.minecraft.NoiseParameterKey;
import nl.kallestruik.noisesampler.minecraft.Xoroshiro128PlusPlusRandom;
import nl.kallestruik.noisesampler.minecraft.noise.LazyDoublePerlinNoiseSampler;
import nl.kallestruik.noisesampler.minecraft.util.MathHelper;
import nl.kallestruik.noisesampler.minecraft.util.Util;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Consumer;

public class SearchCoords {

    // ================= 共享线程池（跨所有 SearchCoords 实例复用，避免每次搜索都创建/销毁线程） =================
    // 缓存线程池：空闲线程会被复用，不会像 newFixedThreadPool 那样每次搜索都新建 OS 线程。
    private static final AtomicInteger POOL_THREAD_COUNTER = new AtomicInteger();
    private static final ThreadFactory DAEMON_THREAD_FACTORY = r -> {
        Thread t = new Thread(r, "seed-search-worker-" + POOL_THREAD_COUNTER.incrementAndGet());
        t.setDaemon(true);
        return t;
    };
    private static final ExecutorService SHARED_EXECUTOR = Executors.newCachedThreadPool(DAEMON_THREAD_FACTORY);

    private final SwampHut swampHut;
    private final GameVersion gameVersion;
    private final MCVersion mcVersion;
    private final WorldPresetMode worldPresetMode;
    private Thread progressThread;
    private volatile boolean isRunning = false;
    private volatile boolean isPaused = false;
    // 用于在调整线程数时，让当前批次的任务尽快自行退出，而不必销毁/重建整个线程池
    private volatile boolean restartRequested = false;
    private final List<String> results = new ArrayList<>();

    // 当前搜索完成信号（替代原来对 executor.isTerminated() / awaitTermination 的轮询）
    private volatile CompletableFuture<Void> currentCompletion = CompletableFuture.completedFuture(null);

    // 保存当前搜索状态，用于动态调整线程数
    private long currentSeed;
    private int currentMinX, currentMaxX, currentMinZ, currentMaxZ;
    private double currentMaxHeight;
    private AtomicLong currentProcessedCount;
    private Consumer<String> currentResultCallback;
    private int currentThreadCount;
    private boolean currentCheckGeneration;

    // ================= 每线程每种子缓存（噪声采样器 + SeedChecker） =================
    private static final ThreadLocal<ThreadSeedResources> THREAD_RESOURCES = new ThreadLocal<>();

    public record ProgressInfo(long processed, long total, double percentage, long elapsedMs, long remainingMs) {
    }

    public SearchCoords(GameVersion gameVersion, WorldPresetMode worldPresetMode) {
        this.gameVersion = gameVersion;
        this.mcVersion = gameVersion.getMcVersion();
        this.worldPresetMode = worldPresetMode;
        this.swampHut = new SwampHut(mcVersion);
    }

    public void startSearch(long seed, int threadCount, int minX, int maxX, int minZ, int maxZ, double maxHeight,
                            Consumer<ProgressInfo> progressCallback, Consumer<String> resultCallback, boolean checkGeneration) {
        // 如果正在运行且处于暂停状态，且线程数变化，则调整线程数
        if (isRunning && isPaused && threadCount != currentThreadCount) {
            adjustThreadCount(threadCount, resultCallback, checkGeneration);
            return;
        }

        if (isRunning) {
            return;
        }
        isRunning = true;
        restartRequested = false;
        results.clear();

        long totalTasks = (long) (maxX - minX) * (maxZ - minZ);

        // 保存当前搜索状态
        currentSeed = seed;
        currentMinX = minX;
        currentMaxX = maxX;
        currentMinZ = minZ;
        currentMaxZ = maxZ;
        currentMaxHeight = maxHeight;
        currentThreadCount = threadCount;
        currentResultCallback = resultCallback;
        currentCheckGeneration = checkGeneration;

        AtomicLong processedCount = new AtomicLong(0);
        currentProcessedCount = processedCount;

        long startTime = System.currentTimeMillis();
        AtomicLong pausedTime = new AtomicLong(0);
        AtomicReference<Long> pauseStartTime = new AtomicReference<>(0L);

        CompletableFuture<Void> completion = submitBatch(seed, threadCount, minX, maxX, minZ, maxZ, maxHeight,
                processedCount, resultCallback, checkGeneration);
        currentCompletion = completion;
        completion.whenCompleteAsync((v, ex) -> isRunning = false, SHARED_EXECUTOR);

        // 进度监控线程：只负责按 100ms 节奏刷新 UI 进度，不再用于探测“任务是否结束”
        progressThread = new Thread(() -> {
            while (isRunning && !completion.isDone()) {
                try {
                    Thread.sleep(100);
                    long processed = processedCount.get();
                    double percentage = (double) processed / totalTasks * 100.0;

                    if (isPaused) {
                        pauseStartTime.updateAndGet(start -> start == 0 ? System.currentTimeMillis() : start);
                    } else {
                        Long pauseStart = pauseStartTime.getAndSet(0L);
                        if (pauseStart > 0) {
                            pausedTime.addAndGet(System.currentTimeMillis() - pauseStart);
                        }
                    }

                    long elapsed = System.currentTimeMillis() - startTime - pausedTime.get();
                    long remaining = processed > 0 ? (elapsed * (totalTasks - processed) / processed) : 0;

                    if (progressCallback != null) {
                        progressCallback.accept(new ProgressInfo(processed, totalTasks, percentage, elapsed, remaining));
                    }
                } catch (InterruptedException e) {
                    break;
                }
            }
            long processed = processedCount.get();
            double percentage = (double) processed / totalTasks * 100.0;
            long elapsed = System.currentTimeMillis() - startTime - pausedTime.get();
            if (progressCallback != null) {
                progressCallback.accept(new ProgressInfo(processed, totalTasks, percentage, elapsed, 0));
            }
        });
        progressThread.setDaemon(true);
        progressThread.start();
    }

    /**
     * 阻塞当前线程直到本次搜索完成——没有轮询、没有 sleep(100)，
     * 一旦所有任务结束会立刻返回。适合批量种子搜索场景使用，
     * 用它替代原来的 `while (isRunning()) Thread.sleep(100);`。
     */
    public void awaitCompletion() {
        try {
            currentCompletion.join();
        } catch (Exception ignored) {
            // 任务被取消/异常时忽略，isRunning 状态已经反映了结果
        }
    }

    private CompletableFuture<Void> submitBatch(long seed, int threadCount, int minX, int maxX, int minZ, int maxZ,
                                                 double maxHeight, AtomicLong processedCount,
                                                 Consumer<String> resultCallback, boolean checkGeneration) {
        int totalX = maxX - minX;
        int chunkSize = Math.max(1, totalX / threadCount);
        List<CompletableFuture<Void>> futures = new ArrayList<>(threadCount);

        for (int i = 0; i < threadCount; i++) {
            int startX = minX + i * chunkSize;
            int endX = (i == threadCount - 1) ? maxX : startX + chunkSize;
            RegionChecker task = new RegionChecker(seed, startX, endX, minZ, maxZ, maxHeight, processedCount, resultCallback, checkGeneration);
            futures.add(CompletableFuture.runAsync(task, SHARED_EXECUTOR));
        }

        return CompletableFuture.allOf(futures.toArray(new CompletableFuture[0]));
    }

    public void stop() {
        isRunning = false;
        isPaused = false;
        restartRequested = true;
        if (progressThread != null) {
            progressThread.interrupt();
        }
    }

    public void pause() {
        isPaused = true;
    }

    public void resume() {
        isPaused = false;
    }

    // 动态调整线程数，保持进度继续。任务是协作式退出的（检查 restartRequested），
    // 不需要销毁/重建整个线程池——线程池本身是共享且常驻的。
    private void adjustThreadCount(int newThreadCount, Consumer<String> resultCallback, boolean checkGeneration) {
        if (newThreadCount < 1) {
            return;
        }

        // 让当前批次的任务尽快退出
        restartRequested = true;
        currentCompletion.join();
        restartRequested = false;

        currentThreadCount = newThreadCount;
        currentResultCallback = resultCallback;
        currentCheckGeneration = checkGeneration;

        CompletableFuture<Void> completion = submitBatch(currentSeed, newThreadCount, currentMinX, currentMaxX,
                currentMinZ, currentMaxZ, currentMaxHeight, currentProcessedCount, currentResultCallback, currentCheckGeneration);
        currentCompletion = completion;
        completion.whenCompleteAsync((v, ex) -> isRunning = false, SHARED_EXECUTOR);

        isPaused = false;
    }

    public boolean isPaused() {
        return isPaused;
    }

    public boolean isRunning() {
        return isRunning;
    }

    public List<String> getResults() {
        return new ArrayList<>(results);
    }

    public GameVersion getGameVersion() {
        return gameVersion;
    }

    public MCVersion getMCVersion() {
        return mcVersion;
    }

    public WorldPresetMode getWorldPresetMode() {
        return worldPresetMode;
    }

    class RegionChecker implements Runnable {
        private final long seed;
        private final int startX;
        private final int endX;
        private final int minZ;
        private final int maxZ;
        private final double maxHeight;
        private final ChunkRand rand;
        private final AtomicLong processedCount;
        private final Consumer<String> resultCallback;
        private final boolean checkGeneration;

        public RegionChecker(long seed, int startX, int endX, int minZ, int maxZ, double maxHeight, AtomicLong processedCount, Consumer<String> resultCallback, boolean checkGeneration) {
            this.seed = seed;
            this.startX = startX;
            this.endX = endX;
            this.minZ = minZ;
            this.maxZ = maxZ;
            this.maxHeight = maxHeight;
            this.rand = new ChunkRand();
            this.processedCount = processedCount;
            this.resultCallback = resultCallback;
            this.checkGeneration = checkGeneration;
        }

        @Override
        public void run() {
            int maxHeightInt = (int) maxHeight;

            try {
                for (int x = startX; x < endX && isRunning && !restartRequested; x++) {
                    for (int z = minZ; z < maxZ && isRunning && !restartRequested; z++) {
                        while (isPaused && isRunning && !restartRequested) {
                            try {
                                Thread.sleep(100);
                            } catch (InterruptedException e) {
                                Thread.currentThread().interrupt();
                                return;
                            }
                        }
                        if (!isRunning || restartRequested) {
                            break;
                        }
                        try {
                            CPos pos = swampHut.getInRegion(seed, x, z, rand);
                            if (!SearchCoords.this.check(seed, 16 * pos.getX(), 16 * pos.getZ(), maxHeightInt)) {
                                continue;
                            }
                            int hutX = 16 * pos.getX();
                            int hutZ = 16 * pos.getZ();
                            Result estimated = checkHeight(seed, hutX, hutZ, mcVersion, worldPresetMode);
                            if (!(estimated.height <= maxHeight)) {
                                continue;
                            }
                            if (worldPresetMode == WorldPresetMode.SINGLE_BIOME || !checkGeneration) {
                                emitResultLine(estimated.toString(), resultCallback);
                            } else {
                                tryCheckHeightByRealGen(pos, estimated, resultCallback);
                            }
                        } finally {
                            processedCount.incrementAndGet();
                        }
                    }
                }
            } finally {
                ThreadSeedResources resources = THREAD_RESOURCES.get();
                if (resources != null && resources.seed == seed && resources.worldPresetMode == worldPresetMode) {
                    resources.clear();
                    THREAD_RESOURCES.remove();
                }
            }
        }

        private void emitResultLine(String resultStr, Consumer<String> resultCallback) {
            synchronized (results) {
                results.add(resultStr);
            }
            if (resultCallback != null) {
                resultCallback.accept(resultStr);
            }
        }

        private void tryCheckHeightByRealGen(CPos pos, Result estimatedHeight, Consumer<String> resultCallback) {
            try {
                checkHeightByRealGen(pos, estimatedHeight, resultCallback);
            } catch (NoClassDefFoundError | ExceptionInInitializerError e) {
                if (e.getCause() != null && e.getCause().getMessage() != null && e.getCause().getMessage().contains("No class provided")) {
                    return;
                }
                throw e;
            }
        }

        private void checkHeightByRealGen(CPos pos, Result estimatedHeight, Consumer<String> resultCallback) {
            int hutX = 16 * pos.getX();
            int hutZ = 16 * pos.getZ();
            Integer generatedFloorY = findGeneratedHutFloorY(seed, hutX, hutZ, worldPresetMode);
            String resultStr;
            if (generatedFloorY == null) {
                resultStr = estimatedHeight.toString() + " x";
            } else {
                double actualHeight = generatedFloorY - 1;
                if (Double.compare(estimatedHeight.height(), actualHeight) != 0) {
                    resultStr = new Result(hutX, hutZ, actualHeight).toString();
                } else {
                    resultStr = estimatedHeight.toString();
                }
            }
            emitResultLine(resultStr, resultCallback);
        }
    }

    // Result类，用于返回坐标和高度
    public record Result(int x, int z, double height) {

        @NotNull
        @Override
        public String toString() {
            return String.format("/tp %d %.0f %d", x, height, z);
        }
    }

    public static Integer findGeneratedHutFloorY(long seed, int hutX, int hutZ, WorldPresetMode worldPresetMode) {
        ThreadSeedResources resources = getThreadResources(seed, worldPresetMode);
        SeedChecker checker = resources.getStructureChecker();
        try {
            for (int y = -55; y <= 128; y++) {
                if (checker.getBlock(hutX + 2, y, hutZ + 2) == Blocks.SPRUCE_PLANKS) {
                    return y;
                }
            }
            return null;
        } finally {
            checker.clearMemory();
        }
    }

    // 精确检查女巫小屋所在区域的地形高度(未生成结构时)
    public static Result checkHeight(long seed, int x, int z, MCVersion mcVersion, WorldPresetMode worldPresetMode) {
        long structureSeed = seed & 281474976710655L;
        ChunkRand rand = new ChunkRand();
        rand.setCarverSeed(structureSeed, x / 16, z / 16, mcVersion);
        float a = rand.nextFloat();
        ThreadSeedResources resources = getThreadResources(seed, worldPresetMode);
        SeedChecker checker = resources.getTerrainChecker();
        try {
            int totalHeight = 0;
            if (a < 0.25F || (a >= 0.5F && a < 0.75F)) {
                for (int i = x; i < x + 7; i++) {
                    for (int j = z; j < z + 9; j++) {
                        boolean checked = false;
                        for (int k = 200; k >= -55 && !checked; k--) {
                            if (!checker.getBlockState(i, k, j).isAir()) {
                                checked = true;
                                totalHeight += k;
                            }
                        }
                    }
                }
            } else {
                for (int i = x; i < x + 9; i++) {
                    for (int j = z; j < z + 7; j++) {
                        boolean checked = false;
                        for (int k = 200; k >= -55 && !checked; k--) {
                            if (!checker.getBlockState(i, k, j).isAir()) {
                                checked = true;
                                totalHeight += k;
                            }
                        }
                    }
                }
            }
            int height = (int) Math.ceil(((double) totalHeight / 63) + 1);
            return new Result(x, z, height);
        } finally {
            checker.clearMemory();
        }
    }

    public boolean check(long seed, int x, int z, int maxHeight) {
        WorldNoiseCache cache = getThreadResources(seed, worldPresetMode).noise;
        int climateX = x + 8;
        int climateZ = z + 8;
        int heightX = x + 3;
        int heightZ = z + 3;

        boolean isSingleBiome = worldPresetMode == WorldPresetMode.SINGLE_BIOME;
        if (!isSingleBiome) {
            double erosionSample = cache.erosion.sample((double) climateX / 4, 0, (double) climateZ / 4);
            if (erosionSample < 0.55) {
                return false;
            }
            double temperature = cache.temperature.sample((double) climateX / 4, 0, (double) climateZ / 4);
            if (mcVersion == MCVersion.v1_18_2) {
                if (temperature < -0.45) {
                    return false;
                }
            } else {
                if (temperature > 0.2 || temperature < -0.45) {
                    return false;
                }
            }
            double ridge = cache.ridge.sample((double) climateX / 4, 0, (double) climateZ / 4);
            if ((ridge > 0.42 && ridge < 0.91) || (ridge < -0.42 && ridge > -0.91)) {
                return false;
            }
            if (gameVersion == GameVersion.V26_2 && ridge <= -0.91) {
                return false;
            }
        }
        if (Entrance(seed, heightX, 50, heightZ, worldPresetMode) >= 0) {
            return false;
        }
        if (Entrance(seed, heightX, 60, heightZ, worldPresetMode) >= 0) {
            return false;
        }
        if (Entrance2(seed, heightX, maxHeight, heightZ, worldPresetMode) >= 0 && Cheese(seed, heightX, maxHeight, heightZ, worldPresetMode) >= 0) {
            return false;
        }
        for (int y = 0; y >= -40; y -= 10) {
            if (maxHeight < y) {
                if (Entrance2(seed, heightX, y, heightZ, worldPresetMode) >= 0 && Cheese(seed, heightX, y, heightZ, worldPresetMode) >= 0) {
                    return false;
                }
            }
        }
        for (int y = 10; y <= 40; y += 10) {
            if (Entrance(seed, heightX, y, heightZ, worldPresetMode) >= 0 && Cheese(seed, heightX, y, heightZ, worldPresetMode) >= 0) {
                return false;
            }
        }
        if (!isSingleBiome && cache.continentalness.sample((double) climateX / 4, 0, (double) climateZ / 4) < -0.11) {
            return false;
        }
        for (int y = maxHeight; y <= 60; y += 10) {
            if (cache.aquiferFloodedness.sample(heightX, y * 0.67, heightZ) > 0.41) {
                return false;
            }
        }
        return true;
    }

    private static ThreadSeedResources getThreadResources(long seed, WorldPresetMode worldPresetMode) {
        ThreadSeedResources resources = THREAD_RESOURCES.get();
        if (resources == null || resources.seed != seed || resources.worldPresetMode != worldPresetMode) {
            if (resources != null) {
                resources.clear();
            }
            resources = new ThreadSeedResources(seed, worldPresetMode);
            THREAD_RESOURCES.set(resources);
        }
        return resources;
    }

    private static final class ThreadSeedResources {
        final long seed;
        final WorldPresetMode worldPresetMode;
        final WorldNoiseCache noise;
        private SeedChecker terrainChecker;
        private SeedChecker structureChecker;

        ThreadSeedResources(long seed, WorldPresetMode worldPresetMode) {
            this.seed = seed;
            this.worldPresetMode = worldPresetMode;
            this.noise = new WorldNoiseCache(seed, worldPresetMode);
        }

        SeedChecker getTerrainChecker() {
            if (terrainChecker == null) {
                terrainChecker = SeedCheckerFactory.create(
                        seed, TargetState.NO_STRUCTURES, SeedCheckerDimension.OVERWORLD, worldPresetMode);
            }
            return terrainChecker;
        }

        SeedChecker getStructureChecker() {
            if (structureChecker == null) {
                structureChecker = SeedCheckerFactory.create(
                        seed, TargetState.STRUCTURES, SeedCheckerDimension.OVERWORLD, worldPresetMode);
            }
            return structureChecker;
        }

        void clear() {
            if (terrainChecker != null) {
                terrainChecker.clearMemory();
            }
            if (structureChecker != null) {
                structureChecker.clearMemory();
            }
        }
    }

    private static class WorldNoiseCache {
        final LazyDoublePerlinNoiseSampler caveEntrance;
        final LazyDoublePerlinNoiseSampler spaghettiRarity;
        final LazyDoublePerlinNoiseSampler spaghettiThickness;
        final LazyDoublePerlinNoiseSampler spaghetti3D1;
        final LazyDoublePerlinNoiseSampler spaghetti3D2;
        final LazyDoublePerlinNoiseSampler spaghettiRoughnessModulator;
        final LazyDoublePerlinNoiseSampler spaghettiRoughness;
        final LazyDoublePerlinNoiseSampler erosion;
        final LazyDoublePerlinNoiseSampler temperature;
        final LazyDoublePerlinNoiseSampler continentalness;
        final LazyDoublePerlinNoiseSampler ridge;
        final LazyDoublePerlinNoiseSampler caveLayer;
        final LazyDoublePerlinNoiseSampler caveCheese;
        final LazyDoublePerlinNoiseSampler aquiferFloodedness;

        WorldNoiseCache(long worldSeed, WorldPresetMode worldPresetMode) {
            Xoroshiro128PlusPlusRandom random = new Xoroshiro128PlusPlusRandom(worldSeed);
            var deriver = random.createRandomDeriver();
            caveEntrance = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, NoiseParameterKey.CAVE_ENTRANCE);
            spaghettiRarity = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, NoiseParameterKey.SPAGHETTI_3D_RARITY);
            spaghettiThickness = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, NoiseParameterKey.SPAGHETTI_3D_THICKNESS);
            spaghetti3D1 = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, NoiseParameterKey.SPAGHETTI_3D_1);
            spaghetti3D2 = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, NoiseParameterKey.SPAGHETTI_3D_2);
            spaghettiRoughnessModulator = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, NoiseParameterKey.SPAGHETTI_ROUGHNESS_MODULATOR);
            spaghettiRoughness = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, NoiseParameterKey.SPAGHETTI_ROUGHNESS);
            NoiseParameterKey erosionKey = worldPresetMode == WorldPresetMode.LARGE_BIOMES ? NoiseParameterKey.EROSION_LARGE : NoiseParameterKey.EROSION;
            NoiseParameterKey temperatureKey = worldPresetMode == WorldPresetMode.LARGE_BIOMES ? NoiseParameterKey.TEMPERATURE_LARGE : NoiseParameterKey.TEMPERATURE;
            NoiseParameterKey continentalnessKey = worldPresetMode == WorldPresetMode.LARGE_BIOMES ? NoiseParameterKey.CONTINENTALNESS_LARGE : NoiseParameterKey.CONTINENTALNESS;
            erosion = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, erosionKey);
            temperature = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, temperatureKey);
            continentalness = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, continentalnessKey);
            ridge = LazyDoublePerlinNoiseSampler.createNoiseSampler(deriver, NoiseParameterKey.RIDGE);

            Xoroshiro128PlusPlusRandom cheeseRandom = new Xoroshiro128PlusPlusRandom(worldSeed);
            var cheeseDeriver = cheeseRandom.createRandomDeriver();
            caveLayer = LazyDoublePerlinNoiseSampler.createNoiseSampler(cheeseDeriver, NoiseParameterKey.CAVE_LAYER);
            caveCheese = LazyDoublePerlinNoiseSampler.createNoiseSampler(cheeseDeriver, NoiseParameterKey.CAVE_CHEESE);

            aquiferFloodedness = LazyDoublePerlinNoiseSampler.createNoiseSampler(
                    new Xoroshiro128PlusPlusRandom(worldSeed).createRandomDeriver(),
                    NoiseParameterKey.AQUIFER_FLUID_LEVEL_FLOODEDNESS);
        }
    }

    public static double Entrance(long worldSeed, int x, int y, int z, WorldPresetMode worldPresetMode) {
        WorldNoiseCache cache = getThreadResources(worldSeed, worldPresetMode).noise;
        double c = cache.caveEntrance.sample(x * 0.75, y * 0.5, z * 0.75) + 0.37 +
                MathHelper.clampedLerp(0.3, 0.0, (10 + (double) y) / 40.0);
        double d = cache.spaghettiRarity.sample(x * 2, y, z * 2);
        double e = NoiseColumnSampler.CaveScaler.scaleTunnels(d);
        double h = Util.lerpFromProgress(cache.spaghettiThickness, x, y, z, 0.065, 0.088);
        double l = NoiseColumnSampler.sample(cache.spaghetti3D1, x, y, z, e);
        double m = Math.abs(e * l) - h;
        double n = NoiseColumnSampler.sample(cache.spaghetti3D2, x, y, z, e);
        double o = Math.abs(e * n) - h;
        double p = MathHelper.clamp(Math.max(m, o), -1.0, 1.0);
        double q = (-0.05 + (-0.05 * cache.spaghettiRoughnessModulator.sample(x, y, z))) *
                (-0.4 + Math.abs(cache.spaghettiRoughness.sample(x, y, z)));
        return Math.min(c, p + q);
    }

    public static double Cheese(long worldSeed, int x, int y, int z, WorldPresetMode worldPresetMode) {
        WorldNoiseCache cache = getThreadResources(worldSeed, worldPresetMode).noise;
        double a = 4 * cache.caveLayer.sample(x, y * 8, z) * cache.caveLayer.sample(x, y * 8, z);
        double b = MathHelper.clamp((0.27 + cache.caveCheese.sample(x, y * 0.6666666666666666, z)), -1, 1);
        return a + b;
    }

    public static double Entrance2(long worldSeed, int x, int y, int z, WorldPresetMode worldPresetMode) {
        WorldNoiseCache cache = getThreadResources(worldSeed, worldPresetMode).noise;
        double d = cache.spaghettiRarity.sample(x * 2, y, z * 2);
        double e = NoiseColumnSampler.CaveScaler.scaleTunnels(d);
        double h = Util.lerpFromProgress(cache.spaghettiThickness, x, y, z, 0.065, 0.088);
        double l = NoiseColumnSampler.sample(cache.spaghetti3D1, x, y, z, e);
        double m = Math.abs(e * l) - h;
        double n = NoiseColumnSampler.sample(cache.spaghetti3D2, x, y, z, e);
        double o = Math.abs(e * n) - h;
        double p = MathHelper.clamp(Math.max(m, o), -1.0, 1.0);
        double q = (-0.05 + (-0.05 * cache.spaghettiRoughnessModulator.sample(x, y, z))) *
                (-0.4 + Math.abs(cache.spaghettiRoughness.sample(x, y, z)));
        return p + q;
    }
}
