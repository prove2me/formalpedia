-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_compensated_kernel_interior_exact
-- name    : AvramDividend.Classical.avram_bvb_obstruction_uniform_compensated_kernel_interior_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:50:55.274919+00:00
-- url     : https://prove2.me/theorems/cc103351-a909-4190-86c4-4d82605dafdf
-- title:
--   Original compensated uniform-negative-mark affine kernel evaluates to y(y−1)/2 for positive sub
-- statement:
--   Original compensated uniform-negative-mark affine kernel evaluates to y(y−1)/2 for positive subunit reserves; the integrand is supported on marks z<−y.
-- source:
--   Exact complementary reserve-domain case split for parent f98142c5. The full integrand, measure, original negative-mark interval and strict crossing convention are unchanged.

import Mathlib
open MeasureTheory Set Real

theorem AvramDividend.Classical.avram_bvb_obstruction_uniform_compensated_kernel_interior_exact (y : ℝ) (hy : 0 < y) (hy1 : y < 1) :
    (∫ z in Ioo (-1 : ℝ) 0,
      (if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
        ∂(volume : Measure ℝ)) = y * (y - 1) / 2 := by sorry
