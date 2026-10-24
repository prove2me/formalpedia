-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_all_times_iff_le_barrier
-- name    : AvramDividend.Classical.barrierStrategy_right_continuous_all_times_iff_le_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:46:01.315997+00:00
-- url     : https://prove2.me/theorems/6be8f3ce-e89e-4ed6-ad5f-9bf72499a7b2
-- title:
--   Exact all-time right-continuity criterion for barrier dividends
-- statement:
--   For each sample path and any nonnegative dividend barrier a, the cumulative barrier dividend path is right-continuous at all nonnegative times if and only if initial capital is at most the barrier. If x≤a the already proved below-barrier theorem supplies continuity for all t. If x>a the initial lump-sum intervention forces a strict right-discontinuity at t=0. The criterion is the mathematically sharp correction of the existing falsely general all-times continuity milestone.
-- source:
--   Direct deduction from proved barrierStrategy_right_continuous_of_le (74159b66) and barrierStrategy_not_right_continuous_at_zero_above_barrier (7377b64b).

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_not_right_continuous_at_zero_above_barrier
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_right_continuous_all_times_iff_le_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (ω : Ω) :
    (∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t) ↔
      x ≤ a := by sorry
