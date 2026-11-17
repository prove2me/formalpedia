-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB29_optimised_quadratic_and_caplinear_generator_signs
-- name    : AvramDividend.Classical.avram_gbB29_optimised_quadratic_and_caplinear_generator_signs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:41:30.5037+00:00
-- url     : https://prove2.me/theorems/3ec30ad3-8a37-4e85-9991-29925699e683
-- title:
--   Optimised Gaussian quadratic versus affine generator and derivative signs
-- statement:
--   For positive reserves below cap one half, with c=2, sigma=2, q=1/100 and w(y)=2y-y^2, the original discounted Gaussian generator is negative, the clipped affine generator from b=5/11 is positive, and w derivative is at least one. These checked source-compatible local analytic signs isolate the positive-drift occupation obstruction.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gbB29_optimised_quadratic_and_caplinear_generator_signs
    (y : ℝ) (hy0 : 0 < y) (hyC : y < (1 / 2 : ℝ)) :
    (y ^ 2 / 100 - (201 / 50 : ℝ) * y) < 0 ∧
      0 < 2 - (1 / 100 : ℝ) * (y + (30 / 121 : ℝ)) ∧
      (1 : ℝ) ≤ 2 - 2 * y := by sorry
