-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_direction_inner_5_6a
-- name    : ConjGrad.ErrorDecrease.direction_inner_5_6a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:55:18.191263+00:00
-- url     : https://prove2.me/theorems/65bf3a69-08c9-4ce1-b4a0-ac47fcd3f03b
-- title:
--   Theorem 5:3, eq. (5:6a) — $(p_i,p_j)=|r_j|^2|p_i|^2/|r_i|^2$ for $i\le j$
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix, let $k,x_0\in\mathbb{R}^n$, and let $r_0,r_1,\dots$ and $p_0,p_1,\dots$ be the residuals and direction vectors of the cg-method (5:1) started at $x_0$. Then for all indices $i\le j$,
--
--   $$
--   (p_i,p_j) = \frac{|r_j|^2\,|p_i|^2}{|r_i|^2}.
--   $$
--
--   In particular $(p_i,p_j)\ge 0$ for all $i\le j$: the direction vectors never make an obtuse angle with each other. In the proof of Theorem 6:3 this relation expresses the inner products $(p_l,p_{i-1})$ through the squared residuals.
--
--   **Formalization Note** The identity is stated for all $i\le j$, without the restriction to steps before termination. After termination the recursion gives $r_j=p_j=0$, and both sides are $0$ (the right side through Lean's convention $t/0=0$ when $r_i=0$).
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), p. 415, Theorem 5:3, eq. (5:6a)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter

open Matrix

namespace ConjGrad.ErrorDecrease

theorem direction_inner_5_6a {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (i j : ℕ) (hij : i ≤ j) :
    (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ j).p =
      ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r) *
        ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) /
        ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) := by sorry

end ConjGrad.ErrorDecrease
