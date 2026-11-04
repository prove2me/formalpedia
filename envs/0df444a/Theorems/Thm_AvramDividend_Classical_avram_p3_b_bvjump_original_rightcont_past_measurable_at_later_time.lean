-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_rightcont_past_measurable_at_later_time
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_rightcont_past_measurable_at_later_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:36:07.221682+00:00
-- url     : https://prove2.me/theorems/b62323c3-74c2-438a-b19a-8b21441d9230
-- title:
--   Every right-continuous past event belongs to each strictly later original filtration
-- statement:
--   For the original filtration, an event measurable at the right-continuous sigma algebra at i is measurable in every original sigma algebra at strictly later r. This is the exact transfer required to instantiate source finite-cylinder compensation from right-continuous future cylinders, with the original Ω and filtration unchanged. No jump compensator or rate is assumed.
-- source:
--   Mathlib.Probability.Process.Filtration rightCont_eq and iInf₂_le; Avram Proposition 4(i).

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_rightcont_past_measurable_at_later_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (i r : ℝ≥0) (hir : i < r)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont i] A) :
    MeasurableSet[𝓕 r] A := by sorry
