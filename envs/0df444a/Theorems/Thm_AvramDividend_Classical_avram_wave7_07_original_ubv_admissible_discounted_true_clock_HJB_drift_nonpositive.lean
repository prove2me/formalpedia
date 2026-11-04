-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_discounted_true_clock_HJB_drift_nonpositive
-- name    : AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_true_clock_HJB_drift_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:02:34.303716+00:00
-- url     : https://prove2.me/theorems/e35a12e0-32d9-4c20-9879-2c1bd96f6d6d
-- title:
--   Canonical UBV admissible true-clock discounted full Lévy generator HJB drift nonpositive
-- statement:
--   With canonical IsAdmissibleLe, extended-real reserve cap C, HJB generator inequality and the source stopped controlled left-limit reserve, localise the positive compact reserve band to a finite C² cutoff Rcap. The original source's true-clock weighted full-generator-HJB theorem and the genuine predictable exponential discount give integrability and nonpositive expectation of the drift over physical time [0,T]. This preserves the original negative jump compensation and Gaussian/drift components, without asserting the missing intrinsic marked-count compensator.
-- source:
--   W7-07 original UBV HJB signed generator drift adapter for W7-08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_true_clock_predictable_weight_HJB_generator_drift_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_true_clock_HJB_drift_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : ENNReal.ofReal v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
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
      Integrable (fun p => Real.exp (-(q * (p.1 : ℝ))) * R p) μ ∧
      (∫ p, Real.exp (-(q * (p.1 : ℝ))) * R p ∂μ) ≤ 0 := by sorry
