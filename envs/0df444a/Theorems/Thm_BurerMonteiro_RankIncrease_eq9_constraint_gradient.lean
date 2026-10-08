-- Prove2me | Theorems.Thm_BurerMonteiro_RankIncrease_eq9_constraint_gradient
-- name    : BurerMonteiro.RankIncrease.eq9_constraint_gradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:38:35.489985+00:00
-- url     : https://prove2.me/theorems/a9539862-74f2-43c5-9554-e1726b416004
-- title:
--   (9), first line: $\nabla_R(A_i\bullet(RR^T)-b_i)=2A_iR$
-- statement:
--   Let $A_i\in\mathcal S^n$ be a symmetric constraint matrix of the SDP, $b_i\in\mathbb R$, and $r$ a positive integer with $r\le n$. For every $R\in\mathbb R^{n\times r}$, the constraint function $R\mapsto A_i\bullet(RR^T)-b_i$ of $(N_r)$ is differentiable at $R$ with gradient
--   $$\nabla_R\big(A_i\bullet(RR^{T})-b_i\big)=2\,A_iR,$$
--   that is, its derivative at $R$ is the linear map $D\mapsto (2A_iR)\bullet D$.
--
--   This is the first of the derivative formulas (9) on which the first- and second-order optimality conditions of $(N_r)$ rest; it identifies the constraint gradients whose linear independence defines a regular point.
--
--   **Formalization Note** The gradient is identified with a matrix through the trace inner product $G\bullet D=\operatorname{trace}(G^TD)$, and the derivative is a Fréchet derivative under the Frobenius norm. Symmetry of $A_i$ is a hypothesis: without it the gradient is $(A_i+A_i^T)R$.
-- source:
--   Burer & Monteiro, A nonlinear programming algorithm for solving semidefinite programs via low-rank factorization (manuscript of March 9, 2001; Math. Program. 95 (2003)), p. 6, Section 2.2, Eq. (9), first line

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

namespace BurerMonteiro.RankIncrease

/-- (9), first line (p. 6): for symmetric `Aᵢ`, the gradient of the constraint function
`R ↦ Aᵢ • (R Rᵀ) − bᵢ` of `(N_r)` is `2 Aᵢ R`, i.e. its derivative at `R` is `D ↦ (2 Aᵢ R) • D`. -/
theorem eq9_constraint_gradient {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m → ℝ) (hA : ∀ i, (A i).IsSymm) {r : ℕ} (hr0 : 0 < r) (hrn : r ≤ n)
    (i : Fin m) (R : Matrix (Fin n) (Fin r) ℝ) :
    HasFDerivAt (fun R' : Matrix (Fin n) (Fin r) ℝ => frob (A i) (R' * R'ᵀ) - b i)
      (frobCLM ((2 : ℝ) • (A i * R))) R := by sorry

end BurerMonteiro.RankIncrease
