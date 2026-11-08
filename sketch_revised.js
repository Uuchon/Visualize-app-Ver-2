// WAVE LAB - 環境音抑制対応・簡素UI・自由Hzレンジ版（p5.js / Web Audio）
// - マイクまたはテスト音を入力として扱う
// - 3秒環境テストで環境ノイズプロファイルを記録
// - 環境ノイズを解析データから減算して色の変化を確認可能
// - 色相軸 / 明度 / 彩度の対応を可視化
// - 上部UIを簡素化し、Hzレンジを自由設定できるようにする

const app = {
  fft: null,
  noiseProfile: null,
  useNoiseSubtraction: true,
  noiseReductionStrength: 0.9,
  minRange: 20,
  maxRange: 20000,
  isCalibrating: false,
  calibrationStart: 0,
  calibrationDuration: 3000,
  micActive: false,
  noiseActive: false,
  dominantFreq: 0,
  dominantAmplitude: 0,
  spectralCentroid: 0,
  spectralSpread: 0,
  perceivedLoudness: 0,
  currentColor: { r: 230, g: 235, b: 240 },
  spectralFlatnessDb: 0,
  currentSaturation: 100,
  harmonicRatio: 0.5,
  spectrumData: [],
  circleRadius: 50,
  history: [],
  settingsOpen: false
};

const PHON_MAX = 90;
const FMIN = 20;
const FMAX = 20000;
const ISO = {
  f: [20,25,31.5,40,50,63,80,100,125,160,200,250,315,400,500,630,800,1000,1250,1600,2000,2500,3150,4000,5000,6300,8000,10000,12500],
  af: [0.532,0.506,0.480,0.455,0.432,0.409,0.387,0.367,0.349,0.330,0.315,0.301,0.288,0.276,0.267,0.259,0.253,0.250,0.246,0.244,0.243,0.243,0.243,0.242,0.242,0.245,0.254,0.271,0.301],
  Lu: [-31.6,-27.2,-23.0,-19.1,-15.9,-13.0,-10.3,-8.1,-6.2,-4.5,-3.1,-2.0,-1.1,-0.4,0.0,0.3,0.5,0.0,-2.7,-4.1,-1.0,1.7,2.5,1.2,-2.1,-7.1,-11.2,-10.7,-3.1],
  Tf: [78.5,68.7,59.5,51.1,44.0,37.5,31.5,26.5,22.1,17.9,14.4,11.4,8.6,6.2,4.4,3.0,2.2,2.4,3.5,1.7,-1.3,-4.2,-6.0,-5.4,-1.5,6.0,12.6,13.9,12.3]
};

class SafeFFT {
  constructor(smoothing = 0.8, fftSize = 2048) {
    const context = typeof getAudioContext === 'function' ? getAudioContext() : null;
    if (!context) throw new Error('Web Audio AudioContext が利用できません');

    this.analyser = context.createAnalyser();
    const allowedSizes = [32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768];
    const safeSize = allowedSizes.includes(fftSize) ? fftSize : 2048;
    this.analyser.fftSize = safeSize;
    this.analyser.smoothingTimeConstant = constrain(smoothing, 0, 1);
    this._data = new Uint8Array(this.analyser.frequencyBinCount);
    this._sourceNode = null;
  }

  setInput(source) {
    if (this._sourceNode) {
      try { this._sourceNode.disconnect(this.analyser); } catch (err) {}
      this._sourceNode = null;
    }
    if (!source) return;

    const node =
      source.output && typeof source.output.connect === 'function'
        ? source.output
        : source.input && typeof source.input.connect === 'function'
          ? source.input
          : source;

    if (!node || typeof node.connect !== 'function') {
      throw new Error('FFT入力からAudioNodeを取得できませんでした');
    }

    node.connect(this.analyser);
    this._sourceNode = node;
  }

  analyze() {
    this.analyser.getByteFrequencyData(this._data);
    return Array.from(this._data);
  }
}

function createSafeFFT(smoothing = 0.3, desiredBins = 4096) {
  const binCount = Math.max(16, Math.min(16384, Math.floor(desiredBins)));
  const powerOfTwo = Math.pow(2, Math.round(Math.log2(binCount)));
  return new SafeFFT(smoothing, powerOfTwo * 2);
}

function ensureFFTReady() {
  if (!app.fft) app.fft = createSafeFFT(0.3, 4096);
}

async function ensureUserAudioStarted() {
  if (typeof userStartAudio === 'function') {
    await userStartAudio();
    return;
  }
  if (typeof getAudioContext === 'function') {
    const ac = getAudioContext();
    if (ac && ac.state === 'suspended') await ac.resume();
  }
}

function safeSetFFTInput(source) {
  ensureFFTReady();
  if (!app.fft) return;
  if (!source) {
    try { if (app.fft._sourceNode) app.fft._sourceNode.disconnect(app.fft.analyser); } catch (err) {}
    app.fft._sourceNode = null;
    return;
  }
  app.fft.setInput(source);
}

function isoParam(arr, freq) {
  const f = constrain(freq, ISO.f[0], ISO.f[ISO.f.length - 1]);
  let i = 0;
  while (i < ISO.f.length - 2 && f > ISO.f[i + 1]) i++;
  const t = (Math.log(f) - Math.log(ISO.f[i])) / (Math.log(ISO.f[i + 1]) - Math.log(ISO.f[i]));
  return arr[i] + (arr[i + 1] - arr[i]) * t;
}

function contourSPL(freq, phon) {
  const af = isoParam(ISO.af, freq);
  const Lu = isoParam(ISO.Lu, freq);
  const Tf = isoParam(ISO.Tf, freq);
  let Af = 4.47e-3 * (Math.pow(10, 0.025 * phon) - 1.15) +
    Math.pow(0.4 * Math.pow(10, (Tf + Lu) / 10 - 9), af);
  Af = Math.max(Af, 1e-9);
  return (10 / af) * Math.log10(Af) - Lu + 94;
}

function phonFromSPL(freq, spl) {
  let lo = 0;
  let hi = 100;
  if (spl <= contourSPL(freq, lo)) return 0;
  if (spl >= contourSPL(freq, hi)) return hi;
  for (let k = 0; k < 20; k++) {
    const mid = (lo + hi) / 2;
    if (contourSPL(freq, mid) < spl) lo = mid;
    else hi = mid;
  }
  return (lo + hi) / 2;
}

function getLoudnessPerceived(freq, amp) {
  if (!freq || !amp) return 0;
  const dbfs = -100 + amp * 70;
  const spl = dbfs + app.splOffset;
  return constrain(phonFromSPL(freq, spl) / PHON_MAX, 0, 1);
}

function hsbColor(h, s, b, a = 255) {
  colorMode(HSB, 360, 100, 100, 255);
  const c = color(h, s, b, a);
  colorMode(RGB, 255);
  return c;
}

function hueFromFreq(f) {
  const lo = Math.log10(app.minRange);
  const hi = Math.log10(app.maxRange);
  const t = (Math.log10(constrain(f, app.minRange, app.maxRange)) - lo) / (hi - lo);
  return t * 270;
}

function satFromFlatness(db) {
  const FLAT_TONAL_DB = -45;
  const FLAT_NOISY_DB = -3;
  return map(db, FLAT_TONAL_DB, FLAT_NOISY_DB, 100, 20, true);
}

function briFromPhon(phon) {
  return map(phon / PHON_MAX, 0.02, 1.0, 30, 100, true);
}

function computeFlatnessDb(spec, nyq) {
  const FLAT_LO_HZ = 50;
  const FLAT_HI_HZ = 10000;
  const len = spec.length;
  const a = Math.max(1, Math.floor(FLAT_LO_HZ / nyq * len));
  const b = Math.min(len, Math.ceil(FLAT_HI_HZ / nyq * len));
  if (b - a < 8) return 0;
  let sumLin = 0;
  let sumDb = 0;
  for (let i = a; i < b; i++) {
    const db = -100 + spec[i] / 255 * 70;
    sumDb += db;
    sumLin += Math.pow(10, db / 10);
  }
  const n = b - a;
  return sumDb / n - 10 * Math.log10(sumLin / n);
}

class AudioProcessor {
  constructor() {
    this.micStream = null;
    this.micSource = null;
    this.micStarted = false;
    this.osc = new p5.Oscillator('sine');
    this.osc.amp(0.2);
    this.oscStarted = false;
  }

  async startMicrophone() {
    await ensureUserAudioStarted();
    if (this.micStarted && this.micStream) {
      safeSetFFTInput(this.micSource);
      return;
    }

    if (!navigator.mediaDevices || typeof navigator.mediaDevices.getUserMedia !== 'function') {
      throw new Error('このブラウザまたは実行環境ではマイク取得APIが使えません。HTTPSまたはlocalhostで開いてください。');
    }

    const stream = await navigator.mediaDevices.getUserMedia({
      audio: {
        echoCancellation: false,
        noiseSuppression: false,
        autoGainControl: false
      }
    });

    try {
      const context = getAudioContext();
      if (context.state === 'suspended') await context.resume();
      const source = context.createMediaStreamSource(stream);
      safeSetFFTInput(source);
      this.micStream = stream;
      this.micSource = source;
      this.micStarted = true;
      app.micActive = true;
    } catch (err) {
      stream.getTracks().forEach(track => track.stop());
      throw err;
    }
  }

  stopMicrophone() {
    try {
      if (this.micSource) this.micSource.disconnect();
      if (this.micStream) this.micStream.getTracks().forEach(track => track.stop());
    } catch (err) {}
    this.micSource = null;
    this.micStream = null;
    this.micStarted = false;
    app.micActive = false;
    safeSetFFTInput(null);
  }

  startOscillator() {
    try {
      if (!this.oscStarted) {
        this.osc.start();
        this.oscStarted = true;
      }
      safeSetFFTInput(this.osc);
      app.noiseActive = true;
    } catch (err) {
      console.warn('Oscillator start error:', err);
    }
  }

  stopOscillator() {
    try {
      if (this.oscStarted) this.osc.stop();
    } catch (err) {}
    this.oscStarted = false;
    app.noiseActive = false;
    safeSetFFTInput(null);
  }

  setFreq(freq) {
    try { this.osc.freq(freq); } catch (err) {}
  }
}

let audioProcessor;
let settingsToggleButton;
let micButton, noiseButton, testButton;
let minFreqSlider, maxFreqSlider, noiseStrengthSlider;
let noiseToggleButton;
let noiseLevelText;
let splOffset = 100;

function setup() {
  createCanvas(windowWidth, windowHeight);
  textFont('sans-serif');
  ensureFFTReady();
  app.minRange = 20;
  app.maxRange = 20000;
  audioProcessor = new AudioProcessor();
  createMainUI();
  createSettingsPanel();
}

function draw() {
  background(250, 252, 255);

  if (app.noiseActive) {
    const sweep = map(sin(frameCount * 0.03), -1, 1, app.minRange, app.maxRange);
    audioProcessor.setFreq(sweep);
  }

  app.spectrumData = app.fft && app.fft.analyser ? app.fft.analyze() : [];
  analyzeFrequencyContent();
  if (app.isCalibrating) handleCalibration();
  pushColorHistory();

  push();
  translate(width / 2, height / 2 - 40);
  updateCircleProperties();
  drawDynamicCircle();
  pop();

  drawStatusPanel();
  drawSpectrumBar();
  drawFrequencyGraph();
  drawInfoText();
  drawHistory();
}

function analyzeFrequencyContent() {
  if (!app.spectrumData || app.spectrumData.length === 0) {
    app.dominantFreq = 0;
    app.dominantAmplitude = 0;
    app.spectralCentroid = 0;
    app.spectralSpread = 0;
    app.perceivedLoudness = 0;
    app.harmonicRatio = 0.5;
    app.currentColor = { r: 230, g: 235, b: 240 };
    return;
  }

  let working = app.spectrumData.slice();

  if (app.noiseProfile && app.useNoiseSubtraction && (app.micActive || app.noiseActive)) {
    const gain = app.noiseReductionStrength;
    for (let i = 0; i < working.length; i++) {
      const base = app.noiseProfile[i] || 0;
      working[i] = Math.max(0, working[i] - base * gain);
    }
  }

  let totalAmp = 0;
  let weightedFreq = 0;
  let maxAmplitude = 0;
  let maxFreqIndex = 0;
  const nyquist = typeof sampleRate === 'function' ? sampleRate() / 2 : 22050;

  for (let i = 1; i < working.length; i++) {
    const amp = working[i];
    if (amp > maxAmplitude) {
      maxAmplitude = amp;
      maxFreqIndex = i;
    }
  }

  app.dominantAmplitude = maxAmplitude / 255;
  app.dominantFreq = (maxFreqIndex * nyquist) / working.length;
  app.perceivedLoudness = getLoudnessPerceived(app.dominantFreq, app.dominantAmplitude);

  for (let i = 1; i < working.length; i++) {
    const amp = working[i];
    if (amp < 5) continue;
    const freq = (i * nyquist) / working.length;
    if (freq < 20 || freq > 20000) continue;
    weightedFreq += freq * amp;
    totalAmp += amp;
  }

  app.spectralCentroid = totalAmp > 0 ? weightedFreq / totalAmp : 0;

  let variance = 0;
  for (let i = 1; i < working.length; i++) {
    const amp = working[i];
    if (amp < 5) continue;
    const freq = (i * nyquist) / working.length;
    if (freq < 20 || freq > 20000) continue;
    variance += amp * Math.pow(freq - app.spectralCentroid, 2);
  }
  app.spectralSpread = totalAmp > 0 ? Math.sqrt(variance / totalAmp) : 0;

  app.spectralFlatnessDb = computeFlatnessDb(working, nyquist);
  app.currentSaturation = lerp(app.currentSaturation, satFromFlatness(app.spectralFlatnessDb), 0.15);
  app.harmonicRatio = 0.5 + (Math.sin(frameCount * 0.05) + 1) * 0.25;
  app.currentColor = calculateCentroidColor();
  app.spectrumData = working;
}

function calculateCentroidColor() {
  if (app.dominantAmplitude < 0.02 || app.spectralCentroid === 0) {
    return { r: 230, g: 235, b: 240 };
  }

  const hueValue = hueFromFreq(app.spectralCentroid);
  const sat = app.currentSaturation;
  const bri = map(app.perceivedLoudness, 0.02, 1.0, 30, 100, true);

  colorMode(HSB, 360, 100, 100);
  const c = color(hueValue, sat, bri);
  const result = { r: red(c), g: green(c), b: blue(c) };
  colorMode(RGB, 255);
  return result;
}

function startCalibration() {
  if (!app.micActive && !app.noiseActive) {
    alert('マイクかテスト音を起動してから環境測定してください');
    return;
  }

  app.isCalibrating = true;
  app.calibrationStart = millis();
  app.noiseProfile = null;
}

function handleCalibration() {
  if (!app.isCalibrating) return;
  const elapsed = millis() - app.calibrationStart;
  const progress = Math.min(100, floor((elapsed / app.calibrationDuration) * 100));

  if (testButton) {
    testButton.html(`⏳ 計測中 ${progress}%`);
    testButton.style('background-color', '#ff9f43');
  }

  if (elapsed < app.calibrationDuration) {
    if (app.spectrumData && app.spectrumData.length > 0) {
      const avg = app.spectrumData;
      if (!app.noiseProfile || app.noiseProfile.length !== avg.length) {
        app.noiseProfile = new Array(avg.length).fill(0);
      }
      for (let i = 0; i < avg.length; i++) {
        app.noiseProfile[i] += avg[i];
      }
    }
    return;
  }

  app.isCalibrating = false;
  testButton.html('⏱️ 3秒環境テスト');
  testButton.style('background-color', '#10ac84');

  if (app.noiseProfile && app.noiseProfile.length > 0) {
    const count = 1;
    const profile = app.noiseProfile.map(v => v / count);
    app.noiseProfile = smoothArray(profile, 3);
    app.useNoiseSubtraction = true;
    noiseLevelText.html('環境ノイズ: 取得済み');
  }
}

function smoothArray(arr, windowSize) {
  const out = new Array(arr.length);
  const half = Math.floor(windowSize / 2);
  for (let i = 0; i < arr.length; i++) {
    let sum = 0;
    let cnt = 0;
    for (let j = i - half; j <= i + half; j++) {
      if (j >= 0 && j < arr.length) {
        sum += arr[j];
        cnt++;
      }
    }
    out[i] = cnt > 0 ? sum / cnt : arr[i];
  }
  return out;
}

function createMainUI() {
  micButton = createButton('🎤 マイク開始');
  micButton.position(20, 20);
  styleButton(micButton, '#4a69bd');
  micButton.mousePressed(async () => {
    try {
      await ensureUserAudioStarted();
      if (!app.micActive) {
        if (app.noiseActive) {
          audioProcessor.stopOscillator();
          app.noiseActive = false;
          noiseButton.html('🔊 スイープ音テスト');
        }
        await audioProcessor.startMicrophone();
        micButton.html('🎤 マイク停止');
      } else {
        audioProcessor.stopMicrophone();
        micButton.html('🎤 マイク開始');
      }
    } catch (err) {
      console.error(err);
      audioProcessor.stopMicrophone();
      micButton.html('🎤 マイク開始');
      alert('マイク起動に失敗しました。HTTPS/localhost、ブラウザの許可を確認してください');
    }
  });

  noiseButton = createButton('🔊 スイープ音テスト');
  noiseButton.position(180, 20);
  styleButton(noiseButton, '#4a69bd');
  noiseButton.mousePressed(async () => {
    await ensureUserAudioStarted();
    if (!app.noiseActive) {
      if (app.micActive) {
        audioProcessor.stopMicrophone();
        micButton.html('🎤 マイク開始');
      }
      audioProcessor.startOscillator();
      noiseButton.html('🔊 テスト音停止');
    } else {
      audioProcessor.stopOscillator();
      noiseButton.html('🔊 スイープ音テスト');
    }
  });

  testButton = createButton('⏱️ 3秒環境テスト');
  testButton.position(340, 20);
  styleButton(testButton, '#10ac84');
  testButton.mousePressed(startCalibration);

  const settingsButton = createButton('⚙️ 設定');
  settingsButton.position(500, 20);
  styleButton(settingsButton, '#6c5ce7');
  settingsButton.mousePressed(() => {
    app.settingsOpen = !app.settingsOpen;
    const panel = document.getElementById('wave-settings-panel');
    if (panel) panel.style.display = app.settingsOpen ? 'block' : 'none';
  });

  noiseLevelText = createDiv('環境ノイズ: 未取得');
  noiseLevelText.position(20, 64);
  noiseLevelText.style('font-size', '12px');
  noiseLevelText.style('color', '#444');
}

function createSettingsPanel() {
  const panel = document.createElement('div');
  panel.id = 'wave-settings-panel';
  panel.style.display = 'none';
  panel.style.position = 'absolute';
  panel.style.left = '20px';
  panel.style.top = '92px';
  panel.style.width = '360px';
  panel.style.padding = '12px';
  panel.style.background = 'rgba(255,255,255,0.9)';
  panel.style.border = '1px solid #dfe6ee';
  panel.style.borderRadius = '12px';
  panel.style.boxShadow = '0 8px 20px rgba(0,0,0,0.08)';
  panel.style.zIndex = '10';

  const title = document.createElement('div');
  title.innerHTML = '<b>周波数レンジとノイズ抑制</b>';
  title.style.fontSize = '13px';
  title.style.marginBottom = '8px';
  panel.appendChild(title);

  const minWrap = document.createElement('div');
  minWrap.style.marginBottom = '8px';
  minWrap.innerHTML = '下限Hz: <span id="range-min-text">20</span>';
  panel.appendChild(minWrap);
  minFreqSlider = createSlider(20, 20000, 20, 1);
  minFreqSlider.position(120, 118);
  minFreqSlider.style('width', '180px');
  minFreqSlider.input(() => {
    app.minRange = Number(minFreqSlider.value());
    if (app.minRange >= app.maxRange) {
      app.minRange = Math.max(20, app.maxRange - 1);
      minFreqSlider.value(app.minRange);
    }
    document.getElementById('range-min-text').textContent = String(app.minRange);
    document.getElementById('range-max-text').textContent = String(app.maxRange);
  });
  panel.appendChild(minFreqSlider.elt);

  const maxWrap = document.createElement('div');
  maxWrap.style.marginBottom = '8px';
  maxWrap.innerHTML = '上限Hz: <span id="range-max-text">20000</span>';
  panel.appendChild(maxWrap);
  maxFreqSlider = createSlider(20, 20000, 20000, 1);
  maxFreqSlider.position(120, 160);
  maxFreqSlider.style('width', '180px');
  maxFreqSlider.input(() => {
    app.maxRange = Number(maxFreqSlider.value());
    if (app.maxRange <= app.minRange) {
      app.maxRange = Math.min(20000, app.minRange + 1);
      maxFreqSlider.value(app.maxRange);
    }
    document.getElementById('range-min-text').textContent = String(app.minRange);
    document.getElementById('range-max-text').textContent = String(app.maxRange);
  });
  panel.appendChild(maxFreqSlider.elt);

  const noiseToggleWrap = document.createElement('div');
  noiseToggleWrap.style.margin = '10px 0';
  noiseToggleWrap.innerHTML = '環境音抑制: ';
  panel.appendChild(noiseToggleWrap);

  noiseToggleButton = createButton('ON');
  noiseToggleButton.position(140, 180);
  styleButton(noiseToggleButton, '#2ecc71');
  noiseToggleButton.mousePressed(() => {
    app.useNoiseSubtraction = !app.useNoiseSubtraction;
    noiseToggleButton.html(app.useNoiseSubtraction ? 'ON' : 'OFF');
    noiseToggleButton.style('background-color', app.useNoiseSubtraction ? '#2ecc71' : '#95a5a6');
  });
  panel.appendChild(noiseToggleButton.elt);

  const strengthWrap = document.createElement('div');
  strengthWrap.style.marginTop = '10px';
  strengthWrap.innerHTML = '抑制強さ: <span id="noise-strength-text">0.90</span>';
  panel.appendChild(strengthWrap);
  noiseStrengthSlider = createSlider(0, 1.5, 0.9, 0.01);
  noiseStrengthSlider.position(130, 220);
  noiseStrengthSlider.style('width', '180px');
  noiseStrengthSlider.input(() => {
    app.noiseReductionStrength = Number(noiseStrengthSlider.value());
    document.getElementById('noise-strength-text').textContent = app.noiseReductionStrength.toFixed(2);
  });
  panel.appendChild(noiseStrengthSlider.elt);

  document.body.appendChild(panel);
  document.getElementById('range-min-text').textContent = String(app.minRange);
  document.getElementById('range-max-text').textContent = String(app.maxRange);
  document.getElementById('noise-strength-text').textContent = app.noiseReductionStrength.toFixed(2);
}

function styleButton(btn, bgColor) {
  btn.style('background-color', bgColor);
  btn.style('color', 'white');
  btn.style('border', 'none');
  btn.style('padding', '8px 12px');
  btn.style('border-radius', '18px');
  btn.style('cursor', 'pointer');
  btn.style('font-weight', 'bold');
  btn.style('font-size', '12px');
  btn.style('width', '150px');
  btn.style('box-shadow', '0 2px 5px rgba(0,0,0,0.08)');
}

function pushColorHistory() {
  app.history.push(app.currentColor);
  if (app.history.length > width) app.history.shift();
}

function drawHistory() {
  const y = height - 42;
  noStroke();
  for (let i = 0; i < app.history.length; i++) {
    const x = map(i, 0, app.history.length, 0, width);
    const w = width / app.history.length + 1;
    const c = app.history[i];
    fill(c.r, c.g, c.b);
    rect(x, y, w, 42);
  }
}

function updateCircleProperties() {
  const target = 60 + app.perceivedLoudness * 250;
  app.circleRadius = lerp(app.circleRadius, target, 0.15);
}

function drawDynamicCircle() {
  const segments = 128;
  const base = app.circleRadius;
  const deformation = (1 - app.harmonicRatio) * 0.4;

  noStroke();
  fill(app.currentColor.r, app.currentColor.g, app.currentColor.b, 220);
  beginShape();
  for (let i = 0; i < segments; i++) {
    const angle = TWO_PI * i / segments;
    const noiseAmount = deformation * sin(angle * 5 + frameCount * 0.05) * base * app.perceivedLoudness;
    const r = base + noiseAmount;
    vertex(r * cos(angle), r * sin(angle));
  }
  endShape(CLOSE);

  stroke(app.currentColor.r, app.currentColor.g, app.currentColor.b);
  strokeWeight(3);
  noFill();
  beginShape();
  for (let i = 0; i < segments; i++) {
    const angle = TWO_PI * i / segments;
    const noiseAmount = deformation * sin(angle * 5 + frameCount * 0.05) * base * app.perceivedLoudness;
    const r = base + noiseAmount;
    vertex(r * cos(angle), r * sin(angle));
  }
  endShape(CLOSE);
}

function drawStatusPanel() {
  fill(40);
  noStroke();
  textSize(13);
  textAlign(LEFT, TOP);
  text(`状態: ${app.micActive ? 'マイク入力中' : app.noiseActive ? 'スイープ音生成中' : '待機中'}`, 20, 150);
  text(`主要周波数: ${app.dominantFreq.toFixed(0)} Hz`, 20, 175);
  text(`スペクトル重心: ${app.spectralCentroid.toFixed(0)} Hz`, 20, 200);
  text(`耳の感度補正大きさ: ${(app.perceivedLoudness * PHON_MAX).toFixed(0)} phon`, 20, 225);
  text(`処理範囲: ${app.minRange.toFixed(0)} Hz 〜 ${app.maxRange.toFixed(0)} Hz`, 20, 250);
  text(`環境音抑制: ${app.useNoiseSubtraction ? 'ON' : 'OFF'}`, 20, 275);
}

function drawSpectrumBar() {
  const x = 20;
  const y = height - 110;
  const w = min(width - 40, 700);
  const h = 25;

  colorMode(HSB, 360, 100, 100);
  for (let i = 0; i < w; i++) {
    const hue = map(i, 0, w, 0, 270);
    stroke(hue, 90, 90);
    line(x + i, y, x + i, y + h);
  }
  colorMode(RGB, 255);

  noFill();
  stroke(180);
  rect(x, y, w, h, 4);

  if (app.spectralCentroid > 0 && app.dominantAmplitude > 0.02) {
    const t = (Math.log10(constrain(app.spectralCentroid, app.minRange, app.maxRange)) - Math.log10(app.minRange)) / (Math.log10(app.maxRange) - Math.log10(app.minRange));
    const markerX = x + t * w;
    fill(30);
    noStroke();
    triangle(markerX, y - 2, markerX - 6, y - 10, markerX + 6, y - 10);
  }

  fill(80);
  textSize(11);
  textAlign(LEFT, TOP);
  text(`低音 赤 (${app.minRange.toFixed(0)}Hz)`, x, y + h + 5);
  textAlign(RIGHT, TOP);
  text(`高音 紫 (${app.maxRange.toFixed(0)}Hz)`, x + w, y + h + 5);
}

function drawFrequencyGraph() {
  const panelWidth = Math.min(420, width - 40);
  const panelHeight = 150;
  const panelX = width - panelWidth - 20;
  const panelY = height - panelHeight - 110;

  fill(245, 247, 250, 240);
  stroke(220);
  rect(panelX, panelY, panelWidth, panelHeight, 8);

  const minFreq = app.minRange;
  const maxFreq = app.maxRange;
  const bandCount = 64;
  const left = panelX + 34;
  const right = panelX + panelWidth - 12;
  const top = panelY + 28;
  const bottom = panelY + panelHeight - 22;
  const plotW = right - left;
  const plotH = bottom - top;

  textSize(9);
  for (const f of [minFreq, minFreq * 2, minFreq * 5, minFreq * 10, maxFreq]) {
    const t = Math.log10(constrain(f, minFreq, maxFreq)) - Math.log10(minFreq);
    const denom = Math.log10(maxFreq) - Math.log10(minFreq) || 1;
    const x = left + (t / denom) * plotW;
    stroke(230);
    line(x, top, x, bottom);
    noStroke();
    fill(90);
    textAlign(CENTER, TOP);
    text(f >= 1000 ? `${(f / 1000).toFixed(0)}k` : String(Math.round(f)), x, bottom + 3);
  }

  if (app.spectrumData && app.spectrumData.length > 0) {
    const nyquist = typeof sampleRate === 'function' ? sampleRate() / 2 : 22050;
    noStroke();
    for (let i = 0; i < bandCount; i++) {
      const f0 = minFreq * Math.pow(maxFreq / minFreq, i / bandCount);
      const f1 = minFreq * Math.pow(maxFreq / minFreq, (i + 1) / bandCount);
      let peak = 0;
      const start = Math.max(1, Math.floor(f0 / nyquist * app.spectrumData.length));
      const end = Math.min(app.spectrumData.length, Math.ceil(f1 / nyquist * app.spectrumData.length));
      for (let j = start; j < end; j++) {
        peak = Math.max(peak, app.spectrumData[j]);
      }
      const bh = Math.max(2, (peak / 255) * plotH);
      const x = left + i * (plotW / bandCount);
      const wBar = Math.max(1, plotW / bandCount - 1);
      fill(hsbColor(hueFromFreq((f0 + f1) / 2), 80, 90));
      rect(x, bottom - bh, wBar, bh, 1);
    }
  }

  fill(70);
  textSize(11);
  textAlign(LEFT, TOP);
  text('FFTスペクトル（ユーザー指定Hzレンジ）', panelX + 10, panelY + 8);
}

function drawInfoText() {
  const panelX = width - 240;
  const panelY = 20;
  fill(40);
  textSize(14);
  textAlign(LEFT, TOP);
  text('環境音を抑えた音色可視化', panelX, panelY);

  fill(100);
  textSize(11);
  text(
    '1. マイクまたはスイープ音を選ぶ\n2. 「⏱️3秒環境テスト」で背景を測定\n3. Hzの範囲とノイズ抑制を調整\n4. 色の変化が環境音影響を減らした状態で見える',
    panelX,
    panelY + 25
  );
}

function windowResized() {
  resizeCanvas(windowWidth, windowHeight);
}

function keyPressed() {
  if (key === 'g' || key === 'G') {
    app.settingsOpen = !app.settingsOpen;
    const panel = document.getElementById('wave-settings-panel');
    if (panel) panel.style.display = app.settingsOpen ? 'block' : 'none';
  }
}

function getAudioContext() {
  if (typeof window !== 'undefined' && window.AudioContext) return new window.AudioContext();
  return null;
}

function setOutputVolume(value) {}

function liveActive() { return app.dominantAmplitude > 0.02 && app.spectralCentroid > 0; }
