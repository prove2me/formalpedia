-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_half_affine_positive_reserve_deriv_eq_one
-- name    : AvramDividend.Classical.avram_bvb_obstruction_half_affine_positive_reserve_deriv_eq_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:59:40.842926+00:00
-- url     : https://prove2.me/theorems/f4b3a2d3-822e-4062-8353-5e98b700cb31
-- title:
--   Positive-reserve derivative of half-unit affine dividend verification candidate equals one
-- statement:
--   At every strictly positive reserve y, the piecewise candidate w(u)=0 for u<0 and 1/2+u otherwise has ordinary derivative equal to one. This gives the exact derivative term required in the original negative-uniform compound Poisson generator integrand.
-- source:
--   On a positive neighbourhood of y, the candidate agrees with u+1/2. Filter.EventuallyEq.deriv_eq and pinned Mathlib deriv_add_const/deriv_id give derivative one without assuming global smoothness across the zero boundary.

import Mathlib
open Filter Real Set
open scoped Topology

theorem AvramDividend.Classical.avram_bvb_obstruction_half_affine_positive_reserve_deriv_eq_one (y : ℝ) (hy : 0 < y) :
    deriv (fun u : ℝ => if u < 0 then 0 else 1 / 2 + u) y = 1 := by sorry
