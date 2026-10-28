-- Prove2me | Theorems.Thm_D1Bound5_finite_tuple_root_relative_norm
-- name    : D1Bound5.finite_tuple_root_relative_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:46.028162+00:00
-- url     : https://prove2.me/theorems/bded2c6e-51cd-4c8b-a78d-e8666428a8fc
-- title:
--   Relative norm bounds for a square root of a large pair product
-- statement:
--   Let $c,d,z$ be complex numbers with $z^2=cd+1$ and $|c||d|\ge4000$. Then
--   $$\left(1-\frac1{4000}\right)|c||d|\le |z|^2
--   \le\left(1+\frac1{4000}\right)|c||d|.$$
--   This converts the additive error in the square relation into a uniform relative error.
-- source:
--   D1Bound5/FiniteClosedWindow.lean, D1Bound5.finite_tuple_root_relative_norm, lines 7-19; original file SHA-256 c76f227fdc7536f8fd4a58375a484ac2d5bdae3cf78c3ac5339546d0024182fc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic

theorem D1Bound5.finite_tuple_root_relative_norm
    (c d z : ℂ) (hz : z^2 = c*d+1) (hCD : 4000 ≤ ‖c‖*‖d‖) :
    (1-1/4000 : ℝ)*‖c‖*‖d‖ ≤ ‖z‖^2 ∧
      ‖z‖^2 ≤ (1+1/4000 : ℝ)*‖c‖*‖d‖ := by sorry
