-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_negative_mark_affine_scalar_hjb_nonpos
-- name    : AvramDividend.Classical.avram_bvb_obstruction_uniform_negative_mark_affine_scalar_hjb_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:42:38.145283+00:00
-- url     : https://prove2.me/theorems/b65bd345-e221-4113-bfef-5e0d22832760
-- title:
--   Scalar HJB excess is nonpositive for unit negative uniform compound Poisson and half-unit affine candidate
-- statement:
--   For y>0, the explicit scalar function g(y)=−3y/2+y²/2 for 0<y<1, and g(y)=−y for y≥1, is nonpositive. This is the analytic HJB residual after integrating negative uniform(-1,0) jumps of a unit-rate compound Poisson process with drift one, discount one, and w(y)=1/2+y for y≥0, zero otherwise.
-- source:
--   Piecewise elementary arithmetic sign for the uniform negative-mark generator excess. The full source generator identity is a separate obligation; this certified polynomial sign is the sound finite-dimensional final step.

import Mathlib
open Real

theorem AvramDividend.Classical.avram_bvb_obstruction_uniform_negative_mark_affine_scalar_hjb_nonpos (y : ℝ) (hy : 0 < y) :
    (if y < 1 then -(3 / 2 : ℝ) * y + (1 / 2 : ℝ) * y ^ 2
     else -y) ≤ 0 := by sorry
