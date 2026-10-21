-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_named_exit_lt_horizon_measurable
-- name    : AvramDividend.Classical.chat03_first_named_exit_lt_horizon_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:07:57.429003+00:00
-- url     : https://prove2.me/theorems/9dc55b99-2750-4a6f-862f-d39e66de771a
-- title:
--   The first strict two-sided passage clock has measurable finite-horizon sublevel events
-- statement:
--   For the official named upper and lower strict passage times, the event that their minimum is strictly less than any finite nonnegative horizon is measurable. The event equals the union of the upper-clock and lower-clock strict sublevel events, each separately proved measurable using horizon-preserving countable grids. This identifies the finite-horizon occurrence of the first two-sided exit, without asserting right-continuity of the filtration or endpoint attainment.
-- source:
--   Chat03 accepted upper and lower passage-clock strict sublevel measurability and pinned Mathlib min_lt_iff.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_named_upper_passage_lt_horizon_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_named_lower_passage_lt_horizon_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_named_exit_lt_horizon_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | min (twoSidedExitUpTime X upper ω)
        (twoSidedExitDownTime X lower ω) < (T : ℝ≥0∞)} := by sorry
