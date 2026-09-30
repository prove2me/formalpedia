-- Prove2me | Theorems.Thm_ConjGrad_Termination_cg_residuals_orthogonal
-- name    : ConjGrad.Termination.cg_residuals_orthogonal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:49:38.37455+00:00
-- url     : https://prove2.me/theorems/296f487f-08b8-4ca1-998c-a965a4b781dc
-- title:
--   Theorem 5:1, eq. (5:3a) — the cg residuals are mutually orthogonal
-- statement:
--   Let $A$ be a real symmetric positive definite $n \times n$ matrix, let $k, x_0 \in \mathbb{R}^n$, and let $r_0, r_1, \dots$ be the residuals produced by the conjugate gradient method (3:1) started at $x_0$. Then
--
--   $$(r_i, r_j) = 0 \qquad (i \ne j).$$
--
--   Mutual orthogonality of the residuals is what bounds the number of nonzero residuals by the dimension $n$.
--
--   **Formalization Note** The statement is for all indices. After the method reaches the solution the residuals are $0$ (see the definition of the iteration), so the relation continues to hold trivially.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 414, Theorem 5:1, eq. (5:3a)

import Mathlib
import Definitions.Def_ConjGrad_Termination_cgIter

open Matrix

namespace ConjGrad.Termination

/-- Theorem 5:1, eq. (5:3a) (Hestenes–Stiefel 1952, p. 414). For a symmetric positive
definite `A`, the residuals `r₀, r₁, …` of the cg-method (3:1) are mutually orthogonal:
`(rᵢ, rⱼ) = 0` for `i ≠ j`. -/
theorem cg_residuals_orthogonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) :
    ∀ i j, i ≠ j → (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ j).r = 0 := by sorry

end ConjGrad.Termination
