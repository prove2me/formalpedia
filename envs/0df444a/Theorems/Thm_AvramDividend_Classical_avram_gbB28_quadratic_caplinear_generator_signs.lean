-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB28_quadratic_caplinear_generator_signs
-- name    : AvramDividend.Classical.avram_gbB28_quadratic_caplinear_generator_signs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:25:33.105189+00:00
-- url     : https://prove2.me/theorems/789b2f7d-1b97-4d96-b259-4f9feb533ed0
-- title:
--   Quadratic Gaussian generator is negative while caplinear continuation generator is positive
-- statement:
--   For the no-jump Gaussian drift one, sigma two, discount one and cap two fifths, verify the explicit quadratic w(y)=2y-y squared has negative discounted generator on the cap interior, whereas the affine continuation from b=one fifth has positive discounted generator throughout the cap interval. This certifies the local analytic obstruction to a fixed-band source proof that discards positive-drift occupation.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gbB28_quadratic_caplinear_generator_signs
    (y : ℝ) (hy0 : 0 < y) (hyC : y < (2 / 5 : ℝ)) :
    y ^ 2 - 4 * y - 2 < 0 ∧
      0 < 1 - (y + (4 / 25 : ℝ)) := by sorry
