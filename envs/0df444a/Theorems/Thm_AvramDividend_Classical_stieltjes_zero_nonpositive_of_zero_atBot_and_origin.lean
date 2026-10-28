-- Prove2me | Theorems.Thm_AvramDividend_Classical_stieltjes_zero_nonpositive_of_zero_atBot_and_origin
-- name    : AvramDividend.Classical.stieltjes_zero_nonpositive_of_zero_atBot_and_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:37:35.93899+00:00
-- url     : https://prove2.me/theorems/f27f0c2e-21c3-475d-b5ed-dac382c936ee
-- title:
--   Stieltjes regulator zero at the left tail and time zero has no nonpositive payment mass
-- statement:
--   A right-continuous monotone Stieltjes regulator that tends to zero at minus infinity and has value zero at the origin assigns zero measure to every nonpositive time. This establishes the support side condition of the first-passage cumulative-measure translation theorem.
-- source:
--   Support lemma for strong-Markov barrier dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380. Apply to the shifted-future running-supremum Stieltjes regulator after showing its origin value and negative-time extension vanish; then hνzero of cumulative translation 50431279 becomes available.

import Mathlib.MeasureTheory.Measure.Stieltjes

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.stieltjes_zero_nonpositive_of_zero_atBot_and_origin
    (f : StieltjesFunction ℝ)
    (hbot : Filter.Tendsto (f : ℝ → ℝ)
      Filter.atBot (nhds (0 : ℝ)))
    (hzero : f 0 = 0) :
    f.measure (Set.Iic (0 : ℝ)) = 0 := by
  sorry
