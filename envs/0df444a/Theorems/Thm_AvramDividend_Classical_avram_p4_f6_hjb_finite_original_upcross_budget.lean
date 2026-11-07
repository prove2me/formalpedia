-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_finite_original_upcross_budget
-- name    : AvramDividend.Classical.avram_p4_f6_hjb_finite_original_upcross_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:11:47.371841+00:00
-- url     : https://prove2.me/theorems/1122a786-0511-44b8-8ed8-24e2b4821d8f
-- title:
--   Finite-clock original mixed Lévy HJB supersolution upper-exit budget
-- statement:
--   For an original Standing spectrally negative Lévy process with Gaussian and nonzero jump components, a top-cap C² HJB supersolution w with slope at least one has its discounted upper-exit expected reward bounded by w(1), when the strict upper exit occurs before downward ruin and by an arbitrary bounded integer horizon n. This is the finite-horizon Ito/Dynkin stochastic core needed to pass to the full killed upcrossing inequality 8d1164b7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_hjb_finite_original_upcross_budget
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
      w b * (∫⁻ ω,
        if twoSidedExitUpTimeCorrected X (b - 1) ω <
             twoSidedExitDownTimeCorrected X (-1) ω ∧
           twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞) then
          ENNReal.ofReal
            (Real.exp (-(q *
              ENNReal.toReal (twoSidedExitUpTimeCorrected X (b - 1) ω))))
        else 0 ∂P).toReal ≤ w 1 := by sorry
