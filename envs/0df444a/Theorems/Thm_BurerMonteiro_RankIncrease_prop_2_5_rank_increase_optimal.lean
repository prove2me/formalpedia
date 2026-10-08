-- Prove2me | Theorems.Thm_BurerMonteiro_RankIncrease_prop_2_5_rank_increase_optimal
-- name    : BurerMonteiro.RankIncrease.prop_2_5_rank_increase_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:39:33.533874+00:00
-- url     : https://prove2.me/theorems/c3b7811c-72bd-4bcb-a142-9519a47e5877
-- title:
--   Proposition 2.5: a regular local minimum of $(N_r)$ whose zero-column extension is a local minimum of $(N_{r+1})$ solves the SDP
-- statement:
--   Let $C, A_1,\dots,A_m\in\mathcal S^n$ be symmetric and $b\in\mathbb R^m$, under the standing assumptions of §2.1, and let $r$ be a positive integer with $r<n$. Suppose $R^*\in\mathbb R^{n\times r}$ satisfies the hypotheses of Proposition 2.3 for $(N_r)$, i.e. $R^*$ is a local minimum of $(N_r)$ and a regular point, with associated multiplier $y^*\in\mathbb R^m$ and $S^*=C-\sum_i y^*_iA_i$, $S^*R^*=0$. Let $\hat R=[\,R^*\ \ 0\,]\in\mathbb R^{n\times(r+1)}$ be the injection of $R^*$, obtained by appending a zero column. If $\hat R$ is a local minimum of $(N_{r+1})$, then
--   $$X^*=R^*(R^*)^{T}\ \text{is optimal for (1)}\quad\text{and}\quad (S^*,y^*)\ \text{is optimal for (3)}.$$
--
--   This is the certificate behind the paper's rank-increase scheme: solve $(N_r)$ for small $r$, and if the zero-column extension is still locally minimal in $(N_{r+1})$, the factorized point is optimal for the SDP; otherwise increase $r$.
--
--   **Formalization Note** The theorem quantifies over every $y$ with $S(y)R^*=0$; by the uniqueness in Proposition 2.3 this is exactly the multiplier associated with $R^*$, so this is the page's statement. Local minima are taken relative to the feasible sets of $(N_r)$ and $(N_{r+1})$, and optimality relative to the whole feasible sets of (1) and (3). The zero column of $\hat R$ is the last one. The standing assumptions and $0<r$ are carried as on the page.
-- source:
--   Burer & Monteiro, A nonlinear programming algorithm for solving semidefinite programs via low-rank factorization (manuscript of March 9, 2001; Math. Program. 95 (2003)), p. 7, Proposition 2.5

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

namespace BurerMonteiro.RankIncrease

/-- Proposition 2.5 (p. 7): let `r < n` and let `R∗ ∈ ℝ^{n×r}` be a regular local minimum of
`(N_r)` with associated multiplier `y∗` (`S∗ R∗ = 0`, `S∗ = C − ∑ᵢ y∗ᵢ Aᵢ`). If the injection
`R̂ ∈ ℝ^{n×(r+1)}` of `R∗` (a zero column appended) is a local minimum of `(N_{r+1})`, then
`X∗ = R∗ R∗ᵀ` is optimal for (1) and `(S∗, y∗)` is optimal for (3). -/
theorem prop_2_5_rank_increase_optimal {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) (hsa : StandingAssumptions C A b) {r : ℕ} (hr0 : 0 < r)
    (hrn : r < n) (R : Matrix (Fin n) (Fin r) ℝ) (hloc : IsNrLocalMin C A b R)
    (hreg : IsRegular A R) (y : Fin m → ℝ) (hy : slack C A y * R = 0)
    (hinj : IsNrLocalMin C A b (inject R)) :
    IsPrimalOptimal C A b (R * Rᵀ) ∧ IsDualOptimal C A b (slack C A y) y := by sorry

end BurerMonteiro.RankIncrease
