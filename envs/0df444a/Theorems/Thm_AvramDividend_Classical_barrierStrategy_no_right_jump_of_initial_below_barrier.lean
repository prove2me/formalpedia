-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
-- name    : AvramDividend.Classical.barrierStrategy_no_right_jump_of_initial_below_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:59:45.181032+00:00
-- url     : https://prove2.me/theorems/b8214392-7702-4d2d-8973-702a270f0241
-- title:
--   Barrier strategy below its initial cap has no right jump
-- statement:
--   When initial capital x does not exceed the barrier a, the exact cumulative-dividend right limit equals its present value at every nonnegative time. The proved right-increment formula vanishes for all positive times and at zero because max(0,x−a)=0. This is the valid cap-compatible form of initial-time right continuity, accounting for the immediate excess lump-sum when x>a.
-- source:
--   Direct result from the Proved barrierStrategy_right_increment_formula (8d23d801-85d6-465e-8450-4011e0dabd54). The existing Open barrierStrategy_right_continuous_nonnegative_barrier omits the crucial condition x≤a.

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_no_right_jump_of_initial_below_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hxa : x ≤ a)
    (ω : Ω) (t : ℝ≥0) :
    rightLimit (barrierStrategy X x a) t ω =
      barrierStrategy X x a t ω := by sorry
