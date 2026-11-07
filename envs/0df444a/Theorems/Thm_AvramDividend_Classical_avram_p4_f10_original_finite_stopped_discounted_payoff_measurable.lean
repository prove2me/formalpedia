-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f10_original_finite_stopped_discounted_payoff_measurable
-- name    : AvramDividend.Classical.avram_p4_f10_original_finite_stopped_discounted_payoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:53:29.54252+00:00
-- url     : https://prove2.me/theorems/1801682b-4a79-4684-bce7-42efb37f747a
-- title:
--   Original corrected two-sided stopped discounted mixed Levy HJB test is measurable
-- statement:
--   Prove the actual Lévy process X evaluated at the corrected upper/lower/horizon stopping time has measurable discounted HJB value, using path right continuity, adaptedness, stopping time measurability and continuousOn candidate with its negative extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f10_original_finite_stopped_discounted_payoff_measurable
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
      Measurable (fun ω => Real.exp (-(q * ENNReal.toReal (τ ω))) *
        w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)) := by sorry
