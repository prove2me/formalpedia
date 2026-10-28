-- Prove2me | Theorems.Thm_D1Bound5_coherent_retained_four_terminal_sizes
-- name    : D1Bound5.coherent_retained_four_terminal_sizes
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:45.137669+00:00
-- url     : https://prove2.me/theorems/ee652b01-8066-45b3-a0da-fa22e363ff17
-- title:
--   Two terminal bounds from repeated retained growth
-- statement:
--   Let $A,B,S,T,C,D$ be real numbers satisfying
--   $$A\ge3,\quad B\ge3,\quad S>0,\quad T>0,\quad S\le T,\quad S\le C,$$
--   $$1000<C,\qquad 16BST<C,\qquad \frac{A^2C^5}{S^2}<D.$$
--   Then
--   $$1000C<D,\qquad 17ABSTC^3<D.$$
--   These are the two terminal-size bounds used by the four-anchor argument.
-- source:
--   D1Bound5/CoherentRetainedFourSizes.lean, D1Bound5.coherent_retained_four_terminal_sizes, lines 38-80; original file SHA-256 f882bd4a0a69601412377b810cf2c65dfd4dc2c6d90a13a2431ad0da2123b8a9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic

theorem D1Bound5.coherent_retained_four_terminal_sizes
    (A B S T C D : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hST : S ≤ T) (hSC : S ≤ C)
    (hC1000 : 1000 < C) (hC : 16*B*S*T < C)
    (hD : A^2*C^5/S^2 < D) :
    1000*C < D ∧ 17*A*B*S*T*C^3 < D := by sorry
