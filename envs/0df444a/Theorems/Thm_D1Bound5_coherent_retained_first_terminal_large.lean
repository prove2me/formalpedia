-- Prove2me | Theorems.Thm_D1Bound5_coherent_retained_first_terminal_large
-- name    : D1Bound5.coherent_retained_first_terminal_large
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:44.38121+00:00
-- url     : https://prove2.me/theorems/451c39ee-ea34-422b-85fe-986ea488654a
-- title:
--   First terminal separation from a retained power gap
-- statement:
--   Let $A,B,S,T,C$ be real numbers such that
--   $$A\ge3,\quad B\ge3,\quad S>0,\quad B\le S\le T,$$
--   $$2ABS<T,\qquad \frac{A^2T^5}{S^2}<C.$$
--   Then
--   $$16BST<C.$$
--   This supplies the separation needed by the four-anchor estimate.
-- source:
--   D1Bound5/CoherentRetainedFourSizes.lean, D1Bound5.coherent_retained_first_terminal_large, lines 5-36; original file SHA-256 f882bd4a0a69601412377b810cf2c65dfd4dc2c6d90a13a2431ad0da2123b8a9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic

theorem D1Bound5.coherent_retained_first_terminal_large
    (A B S T C : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B) (hS : 0 < S)
    (hBS : B ≤ S) (hST : S ≤ T)
    (hfront : 2*A*B*S < T) (hgap : A^2*T^5/S^2 < C) :
    16*B*S*T < C := by sorry
