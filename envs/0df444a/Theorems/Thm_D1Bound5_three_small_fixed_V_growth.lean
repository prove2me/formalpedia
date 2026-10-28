-- Prove2me | Theorems.Thm_D1Bound5_three_small_fixed_V_growth
-- name    : D1Bound5.three_small_fixed_V_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:44.99296+00:00
-- url     : https://prove2.me/theorems/05c970a7-a4e3-44ea-a1b2-be83d75b36bf
-- title:
--   A V-type bound dominates the cubic fixed-extension threshold
-- statement:
--   Let $A,T,C,D$ be real numbers satisfying
--   $$A\ge1,\quad 0<T<85,\quad C\ge10^{40},\qquad
--   \frac{2A^2C^5}{5T^2}<D.$$
--   Then
--   $$10^{38}C^3<D.$$
--   This converts the V-type lower bound into the simpler cubic threshold.
-- source:
--   D1Bound5/ThreeSmallFixedScalar.lean, D1Bound5.three_small_fixed_V_growth, lines 39-61; original file SHA-256 d59d2ffa2f67d68b2084d696be49c307e1d6ca76bebadcdcb67883e86b4bbd55. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic

theorem D1Bound5.three_small_fixed_V_growth
    (A T C D : ℝ) (hA : 1 ≤ A) (hT : 0 < T) (hT85 : T < 85)
    (hC : (10 : ℝ)^40 ≤ C) (hV : (2/5 : ℝ)*A^2*C^5/T^2 < D) :
    (10 : ℝ)^38*C^3 < D := by sorry
