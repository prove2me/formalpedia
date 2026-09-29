-- Prove2me | Theorems.Thm_ConjGrad_Termination_cg_direction_residual
-- name    : ConjGrad.Termination.cg_direction_residual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:51:00.782252+00:00
-- url     : https://prove2.me/theorems/fde5fd9f-8c69-41ba-8397-401a1aa981df
-- title:
--   Theorem 5:1, eq. (5:3c) — $(p_i,r_j)=0$ for $i<j$ and $(p_i,r_j)=|r_i|^2$ for $i\ge j$
-- statement:
--   Let $A$ be a real symmetric positive definite $n \times n$ matrix, let $k, x_0 \in \mathbb{R}^n$, and let $r_i$, $p_i$ be the residuals and directions produced by the conjugate gradient method (3:1) started at $x_0$. Then
--
--   $$(p_i, r_j) = 0 \quad (i < j), \qquad (p_i, r_j) = |r_i|^2 \quad (i \ge j).$$
--
--   With $j = i$ this gives $(p_i, r_i) = |r_i|^2$, which is why the cg step length (3:1b) coincides with the cd step length (4:1a).
--
--   **Formalization Note** The statement is for all indices; after the method reaches the solution the residuals and directions are $0$.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 414, Theorem 5:1, eq. (5:3c)

import Mathlib
import Definitions.Def_ConjGrad_Termination_cgIter

open Matrix

namespace ConjGrad.Termination

/-- Theorem 5:1, eq. (5:3c) (Hestenes–Stiefel 1952, p. 414). For a symmetric positive
definite `A`, the directions and residuals of the cg-method (3:1) satisfy `(pᵢ, rⱼ) = 0`
for `i < j` and `(pᵢ, rⱼ) = |rᵢ|²` for `i ≥ j`. -/
theorem cg_direction_residual {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) :
    (∀ i j, i < j → (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ j).r = 0) ∧
    (∀ i j, j ≤ i →
      (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ j).r = (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) := by sorry

end ConjGrad.Termination
