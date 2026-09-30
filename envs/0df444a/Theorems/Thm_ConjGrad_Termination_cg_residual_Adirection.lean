-- Prove2me | Theorems.Thm_ConjGrad_Termination_cg_residual_Adirection
-- name    : ConjGrad.Termination.cg_residual_Adirection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:51:33.456398+00:00
-- url     : https://prove2.me/theorems/d9f4cdce-a3d7-4473-bd25-aeb0d8c7cef6
-- title:
--   Theorem 5:1, eq. (5:3d) — $(r_i,Ap_i)=(p_i,Ap_i)$ and $(r_i,Ap_j)=0$ for $i\ne j, j+1$
-- statement:
--   Let $A$ be a real symmetric positive definite $n \times n$ matrix, let $k, x_0 \in \mathbb{R}^n$, and let $r_i$, $p_i$ be the residuals and directions produced by the conjugate gradient method (3:1) started at $x_0$. Then
--
--   $$(r_i, Ap_i) = (p_i, Ap_i), \qquad (r_i, Ap_j) = 0 \quad (i \ne j,\ i \ne j + 1).$$
--
--   These relations complete the induction by which the paper proves Theorem 5:1, and they give the alternative formula (3:2b) for $b_i$.
--
--   **Formalization Note** The statement is for all indices; after the method reaches the solution the residuals and directions are $0$.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 414, Theorem 5:1, eq. (5:3d)

import Mathlib
import Definitions.Def_ConjGrad_Termination_cgIter

open Matrix

namespace ConjGrad.Termination

/-- Theorem 5:1, eq. (5:3d) (Hestenes–Stiefel 1952, p. 414). For a symmetric positive
definite `A`, the cg-method (3:1) satisfies `(rᵢ, Apᵢ) = (pᵢ, Apᵢ)`, and `(rᵢ, Apⱼ) = 0`
whenever `i ≠ j` and `i ≠ j + 1`. -/
theorem cg_residual_Adirection {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) :
    (∀ i, (cgIter A k x₀ i).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p) =
      (cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) ∧
    (∀ i j, i ≠ j → i ≠ j + 1 → (cgIter A k x₀ i).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ j).p) = 0) := by sorry

end ConjGrad.Termination
