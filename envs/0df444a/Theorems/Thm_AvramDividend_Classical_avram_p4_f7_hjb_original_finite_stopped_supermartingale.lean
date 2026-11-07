-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_original_finite_stopped_supermartingale
-- name    : AvramDividend.Classical.avram_p4_f7_hjb_original_finite_stopped_supermartingale
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:19:54.895197+00:00
-- url     : https://prove2.me/theorems/8f4671cc-8d0d-4a32-aaaa-d45687a95f53
-- title:
--   Original mixed Levy stopped finite-clock discounted HJB supermartingale expectation
-- statement:
--   An independent non-BV Gaussian-plus-jumps Ito/Dynkin source obligation. For the actual original Levy process, stop at the minimum of the corrected upper, corrected lower, and deterministic n clocks. Under a global top-cap C2 q-HJB supersolution with slope >=1, the expected nonnegative discounted terminal test value does not exceed the initial w(1). Pathwise nonnegative terminal and no-positive-overshoot contact are handled separately in reduction back to the finite original upcross reward target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f7_hjb_original_finite_stopped_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 ≤ b →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      (∫⁻ ω, ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (τ ω))) *
          w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)) ∂P).toReal ≤ w 1 := by sorry
