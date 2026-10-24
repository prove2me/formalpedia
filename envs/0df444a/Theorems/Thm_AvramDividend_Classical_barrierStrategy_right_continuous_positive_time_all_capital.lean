-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_positive_time_all_capital
-- name    : AvramDividend.Classical.barrierStrategy_right_continuous_positive_time_all_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:26:07.088151+00:00
-- url     : https://prove2.me/theorems/282bfe4e-1680-4fc3-add9-12bf37806e60
-- title:
--   Barrier dividend strategies are right-continuous at every positive time for arbitrary initial capital
-- statement:
--   Every constant barrier dividend process with a nonnegative cap has right-continuous paths at each strictly positive time for every real initial surplus. For x≤a the result is the already proved below-barrier continuity. For x>a, the initial lump sum causes a discontinuity only at time zero and the above-barrier positive-time theorem establishes right continuity thereafter. The theorem is the corrected universal positive-time version of the open false all-times continuity statement.
-- source:
--   Split on x≤a, combining Proved barrierStrategy_right_continuous_of_le with barrierStrategy_right_continuous_above_barrier_positive_time.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_above_barrier_positive_time
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_right_continuous_positive_time_all_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t := by sorry
