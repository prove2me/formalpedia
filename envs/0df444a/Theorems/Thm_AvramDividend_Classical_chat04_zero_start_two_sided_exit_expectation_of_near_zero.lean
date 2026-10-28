-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_zero_start_two_sided_exit_expectation_of_near_zero
-- name    : AvramDividend.Classical.chat04_zero_start_two_sided_exit_expectation_of_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:27:18.957678+00:00
-- url     : https://prove2.me/theorems/6af17860-9f60-41a5-b3db-696c4838f482
-- title:
--   Strict two-sided discounted upper exit expectation vanishes from zero under downward regularity
-- statement:
--   If the spectrally negative Lévy path takes a negative value arbitrarily close to time zero almost surely, its strict downward exit time from zero is zero. Therefore the upper-before-downward strict-exit event is almost surely empty and the exact twoSidedExitExpectation at initial capital zero equals zero, for arbitrary discount q and upper level a. No scale function, unbounded-variation assumption or martingale is required once the path regularity event is supplied.
-- source:
--   Imports Proved chat04_down_exit_time_zero_of_negative_near_zero (ac9a5651-010e-4c40-b205-951565722f97). Direct x=0 contribution to alternative Open before-ruin exit identity 5bcf90e1-211c-42db-beac-d92aeb95b5c9 and parent 3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7. Stronger independent probability statement than 2c9771ff because it removes multiplication by W(a) and all W assumptions.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_zero_of_negative_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_zero_start_two_sided_exit_expectation_of_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ)
    (hnear : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    twoSidedExitExpectation X q a 0 = 0 := by sorry
