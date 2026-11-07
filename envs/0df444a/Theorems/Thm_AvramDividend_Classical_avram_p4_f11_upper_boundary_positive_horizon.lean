-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_upper_boundary_positive_horizon
-- name    : AvramDividend.Classical.avram_p4_f11_upper_boundary_positive_horizon
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T18:46:02.699396+00:00
-- url     : https://prove2.me/theorems/43818f4a-c36a-4e7a-8872-8cde2601b496
-- title:
--   Positive-horizon original top-boundary stopped HJB expectation
-- statement:
--   For the original non-BV Lévy process with nonzero Gaussian and jump parts, establish the discounted potential expectation bound when the upper exit barrier coincides with initial reserve. This isolates right-sided instantaneous upper-passage regularity and its terminal contact from the interior stochastic budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f11_upper_boundary_positive_horizon
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
    ∀ n : ℕ, 0 < n →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (1 - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
          w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) ≤ w 1 := by sorry
