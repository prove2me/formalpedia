-- Prove2me | Theorems.Thm_BurerMonteiro_RankIncrease_eq9_lagrangian_gradient
-- name    : BurerMonteiro.RankIncrease.eq9_lagrangian_gradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:38:43.241977+00:00
-- url     : https://prove2.me/theorems/71555de9-9da0-4dd8-bab6-ff83f1fe4b49
-- title:
--   (9), second line: $\nabla_R L(R,y)=2SR$
-- statement:
--   Let $C, A_1,\dots,A_m\in\mathcal S^n$ be symmetric, $b\in\mathbb R^m$, and $r$ a positive integer with $r\le n$. Let $L(R,y)=C\bullet(RR^T)-\sum_{i=1}^m y_i(A_i\bullet(RR^T)-b_i)$ be the Lagrangian (7) of $(N_r)$ and $S=C-\sum_i y_iA_i$ as in (8). For every $R\in\mathbb R^{n\times r}$ and $y\in\mathbb R^m$,
--   $$\nabla_R L(R,y)=2\,SR,$$
--   that is, the derivative of $R\mapsto L(R,y)$ at $R$ is the linear map $D\mapsto(2SR)\bullet D$.
--
--   This formula turns the stationarity condition $\nabla_RL(R,y)=0$ into the matrix equation $SR=0$, which is how Propositions 2.3 and 2.4 express first-order optimality.
--
--   **Formalization Note** The gradient is identified with a matrix through $G\bullet D=\operatorname{trace}(G^TD)$; the derivative is a Fréchet derivative under the Frobenius norm. The data are symmetric by hypothesis.
-- source:
--   Burer & Monteiro, A nonlinear programming algorithm for solving semidefinite programs via low-rank factorization (manuscript of March 9, 2001; Math. Program. 95 (2003)), p. 6, Section 2.2, Eq. (9), second line

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

namespace BurerMonteiro.RankIncrease

/-- (9), second line (p. 6): for symmetric data, the gradient of the Lagrangian (7) in `R` is
`∇_R L(R, y) = 2 S R` with `S = C − ∑ᵢ yᵢ Aᵢ` as in (8). -/
theorem eq9_lagrangian_gradient {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) {r : ℕ} (hr0 : 0 < r) (hrn : r ≤ n)
    (R : Matrix (Fin n) (Fin r) ℝ) (y : Fin m → ℝ) :
    HasFDerivAt (fun R' : Matrix (Fin n) (Fin r) ℝ => lagrangian C A b R' y)
      (frobCLM ((2 : ℝ) • (slack C A y * R))) R := by sorry

end BurerMonteiro.RankIncrease
