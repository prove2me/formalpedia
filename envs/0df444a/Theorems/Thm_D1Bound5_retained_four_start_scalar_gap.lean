-- Prove2me | Theorems.Thm_D1Bound5_retained_four_start_scalar_gap
-- name    : D1Bound5.retained_four_start_scalar_gap
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:47.422238+00:00
-- url     : https://prove2.me/theorems/7cfd2194-0e59-4ae4-9085-e8e6c57a8ea3
-- title:
--   A seventh-power terminal gap from the four-anchor form
-- statement:
--   Let $A,B,S,T,C,D,Z,L$ be real numbers with
--   $$A,B\ge3,\quad S,T,Z>0,\quad S,T\le C,\quad C>1000,$$
--   $$16BST<C,\qquad \frac{A^2C^5}{S^2}<D,$$
--   $$\frac{3999}{4000}CD<Z^2\le CD+1,\qquad 1\le L,$$
--   $$L<\frac{13BS^2T^3}{Z}+\frac{49ST^2Z}{50AC^4}.$$
--   Then
--   $$\frac{A^2C^7}{S^2T^4}<D.$$
--   This strengthens the retained fifth-power growth to the terminal gap required by the next step.
-- source:
--   D1Bound5/RetainedFourScalar.lean, D1Bound5.retained_four_start_scalar_gap, lines 47-100; original file SHA-256 3040f89836f5fb18966062816d6227f8384c92971a8577d838077bec13d311bf. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic

theorem D1Bound5.retained_four_start_scalar_gap
    (A B S T C D Z L : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hSC : S ≤ C) (hTC : T ≤ C)
    (hC1000 : 1000 < C) (hZ : 0 < Z)
    (hC : 16*B*S*T < C)
    (hD : A^2*C^5/S^2 < D)
    (hrootlo : (3999/4000 : ℝ)*C*D < Z^2)
    (hroothi : Z^2 ≤ C*D+1)
    (hL : 1 ≤ L)
    (hupper : L < 13*B*S^2*T^3/Z + (49/50 : ℝ)*S*T^2*Z/(A*C^4)) :
    A^2*C^7/(S^2*T^4) < D := by sorry
