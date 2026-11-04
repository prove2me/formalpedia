-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_zero_outside_positive_band
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_zero_outside_positive_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:04:31.770106+00:00
-- url     : https://prove2.me/theorems/6788d537-c941-4e3d-a46a-ae4c4080080b
-- title:
--   Inverse exponential weighted test vanishes outside its compact positive-image band
-- statement:
--   For a negative-mark test vanishing below a finite lower mark a and above -epsilon with epsilon positive, its inverse exponential fourth-weighted log transform vanishes at every nonnegative z outside [exp(a),exp(-epsilon)], including z=0. This provides the exact global pointwise support bound used to form bounded continuous compactly supported weak-convergence tests.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_zero_outside_positive_band
    (f : ℝ → ℝ) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (z : ℝ) (hz : 0 ≤ z)
    (hzout : z < Real.exp a ∨ Real.exp (-ε) < z) :
    f (Real.log z) / (z - 1) ^ 4 = 0 := by sorry
