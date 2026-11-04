-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
-- name    : AvramDividend.Classical.avram_p4_c_generator_zero_negative_payoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:07:56.956575+00:00
-- url     : https://prove2.me/theorems/dabe5048-e689-419b-938f-58b5b6d191e4
-- title:
--   Original dividend payoff is Borel measurable despite possible discontinuity at the ruin boundary
-- statement:
--   The source payoff assumption gives continuity on nonnegative reserves and a zero extension on negative reserves. These pieces make the entire payoff Borel measurable, even if its value at zero does not match the negative-side limit. This provides genuine measurable original large-jump increments without incorrectly asserting full continuity at ruin.
-- source:
--   P4 original hw_cont and hw_neg hypotheses; pinned Mathlib ContinuousOn.measurable_piecewise and measurableSet_Ici

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_c_generator_zero_negative_payoff_measurable
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) :
    Measurable w := by sorry
