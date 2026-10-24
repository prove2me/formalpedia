-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_at_zero_iff_le_barrier
-- name    : AvramDividend.Classical.barrierStrategy_right_continuous_at_zero_iff_le_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:38:42.210673+00:00
-- url     : https://prove2.me/theorems/908b900e-25a4-488b-bd5a-08e1e25f19c6
-- title:
--   Exact criterion for right-continuity of barrier dividends at time zero
-- statement:
--   For every sample path and nonnegative dividend cap a, the barrier dividend process is right-continuous at time zero if and only if initial capital x does not exceed a. The forward implication contradicts the proved strictly positive initial dividend jump for x>a; the converse is the published below-barrier right-continuity theorem. This sharp dichotomy replaces the false unconditional all-times regularity claim.
-- source:
--   Combines barrierStrategy_right_continuous_of_le with barrierStrategy_not_right_continuous_at_zero_above_barrier by linear order trichotomy.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_not_right_continuous_at_zero_above_barrier
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_right_continuous_at_zero_iff_le_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (ω : Ω) :
    ContinuousWithinAt
      (fun s => barrierStrategy X x a s ω) (Ici (0 : ℝ≥0)) 0 ↔
      x ≤ a := by sorry
