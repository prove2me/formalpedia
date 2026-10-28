-- Prove2me | Theorems.Thm_D1Bound5_retained_four_first_term_lt
-- name    : D1Bound5.retained_four_first_term_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:45.069409+00:00
-- url     : https://prove2.me/theorems/869af36e-0dc7-478c-8d33-0f70ef45a74d
-- title:
--   The first four-anchor summand is below one percent
-- statement:
--   Let $A,B,S,T,C,D,Z$ be real numbers satisfying
--   $$A\ge3,\quad B\ge3,\quad S,T,Z>0,$$
--   $$16BST<C,\qquad \frac{A^2C^5}{S^2}<D,\qquad
--   \frac{3999}{4000}CD<Z^2.$$
--   Then
--   $$\frac{13BS^2T^3}{Z}<\frac1{100}.$$
--   This isolates the small first summand of the four-anchor form.
-- source:
--   D1Bound5/RetainedFourScalar.lean, D1Bound5.retained_four_first_term_lt, lines 5-45; original file SHA-256 3040f89836f5fb18966062816d6227f8384c92971a8577d838077bec13d311bf. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic

theorem D1Bound5.retained_four_first_term_lt
    (A B S T C D Z : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hZ : 0 < Z)
    (hC : 16*B*S*T < C)
    (hD : A^2*C^5/S^2 < D)
    (hroot : (3999/4000 : ℝ)*C*D < Z^2) :
    13*B*S^2*T^3/Z < (1/100 : ℝ) := by sorry
