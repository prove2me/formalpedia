-- Prove2me | Theorems.Thm_BurerMonteiro_RankIncrease_eq9_lagrangian_second_derivative
-- name    : BurerMonteiro.RankIncrease.eq9_lagrangian_second_derivative
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:38:53.971993+00:00
-- url     : https://prove2.me/theorems/c3cf4d76-267f-4097-8827-f256079337d5
-- title:
--   (9), third line: $L''_{RR}(R,y)[D,D]=2S\bullet(DD^T)$
-- statement:
--   Let $C, A_1,\dots,A_m\in\mathcal S^n$ be symmetric, $b\in\mathbb R^m$, $r$ a positive integer with $r\le n$, $L$ the Lagrangian (7) of $(N_r)$ and $S=C-\sum_i y_iA_i$. For every $R, D\in\mathbb R^{n\times r}$ and $y\in\mathbb R^m$, the second derivative of the Lagrangian in $R$ in the direction $D$ is
--   $$L''_{RR}(R,y)[D,D]=2\,S\bullet(DD^{T}),$$
--   that is, the function $t\mapsto L(R+tD,y)$ has second derivative $2\,S\bullet(DD^T)$ at $t=0$.
--
--   This is the curvature formula behind the second-order necessary condition (11) of Proposition 2.3.
--
--   **Formalization Note** The second derivative along $D$ is expressed as the derivative at $0$ of $t\mapsto \frac{d}{ds}L(R+sD,y)\big|_{s=t}$; since $L(\cdot,y)$ is quadratic this is the bilinear second derivative evaluated at $(D,D)$. It is not encoded as a Taylor expansion.
-- source:
--   Burer & Monteiro, A nonlinear programming algorithm for solving semidefinite programs via low-rank factorization (manuscript of March 9, 2001; Math. Program. 95 (2003)), p. 6, Section 2.2, Eq. (9), third line

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

namespace BurerMonteiro.RankIncrease

/-- (9), third line (p. 6): for symmetric data, the second derivative of the Lagrangian (7) in
`R` along a direction `D ∈ ℝ^{n×r}` is `L''_RR(R, y)[D, D] = 2 S • (D Dᵀ)`, i.e. the second
derivative of `t ↦ L(R + t D, y)` at `t = 0` equals `2 S • (D Dᵀ)`. -/
theorem eq9_lagrangian_second_derivative {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) {r : ℕ} (hr0 : 0 < r) (hrn : r ≤ n)
    (R D : Matrix (Fin n) (Fin r) ℝ) (y : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => lagrangian C A b (R + s • D) y) t)
      (2 * frob (slack C A y) (D * Dᵀ)) 0 := by sorry

end BurerMonteiro.RankIncrease
