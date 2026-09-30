-- Prove2me | Theorems.Thm_ConjGrad_Termination_cg_directions_conjugate
-- name    : ConjGrad.Termination.cg_directions_conjugate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:50:18.004022+00:00
-- url     : https://prove2.me/theorems/03ef5f1d-8a70-496c-a2a2-11921066d0dc
-- title:
--   Theorem 5:1, eq. (5:3b) — the cg directions are mutually conjugate
-- statement:
--   Let $A$ be a real symmetric positive definite $n \times n$ matrix, let $k, x_0 \in \mathbb{R}^n$, and let $p_0, p_1, \dots$ be the direction vectors produced by the conjugate gradient method (3:1) started at $x_0$. Then
--
--   $$(p_i, Ap_j) = 0 \qquad (i \ne j).$$
--
--   This is the relation that makes the cg-method a method of conjugate directions.
--
--   **Formalization Note** The statement is for all indices; after the method reaches the solution the directions are $0$.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 414, Theorem 5:1, eq. (5:3b)

import Mathlib
import Definitions.Def_ConjGrad_Termination_cgIter

open Matrix

namespace ConjGrad.Termination

/-- Theorem 5:1, eq. (5:3b) (Hestenes–Stiefel 1952, p. 414). For a symmetric positive
definite `A`, the directions `p₀, p₁, …` of the cg-method (3:1) are mutually conjugate:
`(pᵢ, Apⱼ) = 0` for `i ≠ j`. -/
theorem cg_directions_conjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) :
    ∀ i j, i ≠ j → (cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ j).p) = 0 := by sorry

end ConjGrad.Termination
