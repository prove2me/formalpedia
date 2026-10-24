-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_above_barrier_positive_time
-- name    : AvramDividend.Classical.barrierStrategy_right_continuous_above_barrier_positive_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:22:48.443131+00:00
-- url     : https://prove2.me/theorems/31d67fe3-a6d8-4958-8f75-860ed448daeb
-- title:
--   An above-barrier dividend process is right-continuous at every strictly positive time
-- statement:
--   Although the barrier dividend path started above the barrier has a positive jump immediately after time zero, it remains right-continuous at every strictly positive time. On a right-neighbourhood of any t>0 the formula is the continuous sum of the constant initial excess and the right-continuous barrier dividend process started from the barrier. This corrects the scope of the earlier open all-times continuity assertion.
-- source:
--   Deduction from Proved barrierStrategy_eq_add_initial_excess_above_barrier and barrierStrategy_right_continuous. Does not assume or imply right continuity at time zero for x>a.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Mathlib.Topology.Algebra.Order.Field
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_right_continuous_above_barrier_positive_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (hax : a < x) (ω : Ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t := by sorry
