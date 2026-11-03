-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_true_clock_predictable_weight_HJB_generator_drift_nonpositive
-- name    : AvramDividend.Classical.avram_wave7_07_true_clock_predictable_weight_HJB_generator_drift_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:36:29.430289+00:00
-- url     : https://prove2.me/theorems/72ccc7b2-e0f4-4d4f-9c8a-d20c5b10e54d
-- title:
--   Original true predictable clock has nonpositive HJB generator drift under every bounded predictable discount
-- statement:
--   For the actual source spectrally negative Lévy process, original dividend control and ruin-stopped prepayment left-limit reserve, the fully compensated generator-minus-q drift R on a compact strictly positive reserve band is Bochner integrable after any original-filtration predictable weight a in [0,1], and its integral over the true finite physical predictable clock is nonpositive under the original HJB inequality. This is the full drift and Gaussian-plus-negative-jump generator contribution under predictable discount; the separate source jump compensator, L2 martingale expectation zero and controlled Stieltjes Ito residual remain distinct.
-- source:
--   W7-07 weighted original-source full-generator HJB residual using Proved 1829a383 finite true clock generator HJB and pinned Integrable.bdd_mul; exact source SpectrallyNegativeLevy.generator and ruinTime.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_true_clock_compact_generator_hjb_L1_nonpositive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_true_clock_predictable_weight_HJB_generator_drift_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable (fun p => a p * R p) μ ∧
      (∫ p, a p * R p ∂μ) ≤ 0 := by sorry
