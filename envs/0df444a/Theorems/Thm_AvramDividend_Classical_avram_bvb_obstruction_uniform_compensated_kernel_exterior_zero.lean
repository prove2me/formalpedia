-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_compensated_kernel_exterior_zero
-- name    : AvramDividend.Classical.avram_bvb_obstruction_uniform_compensated_kernel_exterior_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:50:56.524195+00:00
-- url     : https://prove2.me/theorems/5969c745-15c3-44c2-83ef-30fd96ac55ff
-- title:
--   Original compensated uniform-negative-mark affine kernel vanishes for reserves at least one bec
-- statement:
--   Original compensated uniform-negative-mark affine kernel vanishes for reserves at least one because no negative unit mark can cross below zero.
-- source:
--   Exact complementary reserve-domain case split for parent f98142c5. The full integrand, measure, original negative-mark interval and strict crossing convention are unchanged.

import Mathlib
open MeasureTheory Set Real

theorem AvramDividend.Classical.avram_bvb_obstruction_uniform_compensated_kernel_exterior_zero (y : ℝ) (hy : 1 ≤ y) :
    (∫ z in Ioo (-1 : ℝ) 0,
      (if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
        ∂(volume : Measure ℝ)) = (0 : ℝ) := by sorry
