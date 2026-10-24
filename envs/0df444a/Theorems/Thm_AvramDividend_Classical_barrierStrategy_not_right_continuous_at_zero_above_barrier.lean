-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_not_right_continuous_at_zero_above_barrier
-- name    : AvramDividend.Classical.barrierStrategy_not_right_continuous_at_zero_above_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:29:31.006714+00:00
-- url     : https://prove2.me/theorems/7377b64b-3979-4d9b-946b-0d2a6da883ee
-- title:
--   An above-barrier strategy has a genuine right-discontinuity at time zero
-- statement:
--   For a spectrally negative Levy model, any nonnegative barrier a and any initial capital x>a, the barrier dividend process fails to be right-continuous at time zero. Its nondecreasing path must satisfy rightLimit D 0 = D 0 under right-continuity. The proved initial lump-sum theorem asserts instead that rightLimit D 0−D 0 is strictly positive, yielding a contradiction. This rigorously refutes the above-barrier case of the existing open all-time right-continuity theorem.
-- source:
--   Direct contradiction from Proved barrierStrategy_isDividendStrategy_nonnegative_barrier (501af29f), rightLimit_eq_of_monotone_right_continuous (1785b131), and barrierStrategy_initial_right_jump_positive (8ca9a9f5).

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_right_jump_positive
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_not_right_continuous_at_zero_above_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (hax : a < x) (ω : Ω) :
    ¬ ContinuousWithinAt
      (fun s => barrierStrategy X x a s ω) (Ici (0 : ℝ≥0)) 0 := by sorry
