-- Prove2me | Theorems.Thm_EllipsoidGLS_Rounded_inv_Astar
-- name    : EllipsoidGLS.Rounded.inv_Astar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:23:07.530728+00:00
-- url     : https://prove2.me/theorems/4218072f-4790-45e5-ac6e-26696fe9b016
-- title:
--   Proof of Lemma (2.1), (13), p. 174 — inverse of the updated matrix A_k*; A_k* is positive definite
-- statement:
--   Let $n\ge 2$, let $A$ be a symmetric positive definite $n\times n$ real matrix and let $a\in\mathbb{R}^n$ be nonzero. Put $b=Aa/\sqrt{a^{\mathsf T}Aa}$ and
--   $$A^*=\frac{2n^2+3}{2n^2}\left(A-\frac{2}{n+1}\,bb^{\mathsf T}\right),$$
--   the matrix update of the rounded ellipsoid method. Then $A^*$ is positive definite and
--   $$(A^*)^{-1}=\frac{2n^2}{2n^2+3}\left(A^{-1}+\frac{2}{n-1}\cdot\frac{aa^{\mathsf T}}{a^{\mathsf T}Aa}\right).$$
--
--   This explicit inverse is what the paper uses to control the smallest eigenvalue of the next matrix (Lemma (2.1)) and to verify that the new ellipsoid contains the retained part of the body (Lemma (2.3)).
--
--   **Formalization Note** Positive definiteness is Mathlib's `Matrix.PosDef` (over $\mathbb{R}$ it includes symmetry), and $M^{-1}$ is Mathlib's matrix inverse; the conclusion asserts the formula for the genuine inverse, since $A^*$ is shown nonsingular. The page states (13) for the step's matrix $A_k$ and cut vector $a$; here it is stated for an arbitrary positive definite $A$ and nonzero $a$, which is the content of the computation.
-- source:
--   Grötschel, Lovász, Schrijver, The ellipsoid method and its consequences in combinatorial optimization, Combinatorica 1 (1981), p. 174, proof of Lemma (2.1), (13)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic
import Definitions.Def_EllipsoidGLS_Rounded_Run

namespace EllipsoidGLS.Rounded

open Matrix

theorem inv_Astar {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (Astar A a).PosDef ∧
      (Astar A a)⁻¹ = (2 * (n : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2 + 3)) •
        (A⁻¹ + ((2 / ((n : ℝ) - 1)) * (a ⬝ᵥ A.mulVec a)⁻¹) • vecMulVec a a) := by sorry

end EllipsoidGLS.Rounded
