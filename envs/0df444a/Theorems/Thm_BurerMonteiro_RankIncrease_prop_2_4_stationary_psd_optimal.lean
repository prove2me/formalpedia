-- Prove2me | Theorems.Thm_BurerMonteiro_RankIncrease_prop_2_4_stationary_psd_optimal
-- name    : BurerMonteiro.RankIncrease.prop_2_4_stationary_psd_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:39:25.322484+00:00
-- url     : https://prove2.me/theorems/9b0b92cb-5e99-4716-b2fc-150500515f58
-- title:
--   Proposition 2.4: a stationary point of $(N_r)$ with $S^*\succeq0$ gives optimal $X^*=R^*R^{*T}$ and $(S^*,y^*)$
-- statement:
--   Let $C, A_1,\dots,A_m\in\mathcal S^n$ be symmetric and $b\in\mathbb R^m$, under the standing assumptions of §2.1, and let $r$ be a positive integer with $r\le n$. Let $R^*\in\mathbb R^{n\times r}$ be a stationary point of $(N_r)$: $R^*$ is feasible and there is $y^*\in\mathbb R^m$ with $\nabla_RL(R^*,y^*)=0$. If the associated matrix $S^*=C-\sum_i y^*_iA_i$ is positive semidefinite, then
--   $$X^*=R^*(R^*)^{T}\ \text{is optimal for (1)}\quad\text{and}\quad (S^*,y^*)\ \text{is optimal for (3)}.$$
--
--   This is a sufficient condition, valid for every $r$, under which a point of the factorized problem certifies optimality for the full SDP.
--
--   **Formalization Note** Stationarity is feasibility plus vanishing of the Fréchet derivative of $R\mapsto L(R,y^*)$ at $R^*$; it contains no sign condition on $S^*$, which is a separate hypothesis. Optimality is over the whole feasible sets of (1) and (3).
-- source:
--   Burer & Monteiro, A nonlinear programming algorithm for solving semidefinite programs via low-rank factorization (manuscript of March 9, 2001; Math. Program. 95 (2003)), p. 7, Proposition 2.4

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

namespace BurerMonteiro.RankIncrease

/-- Proposition 2.4 (p. 7): if `R∗` is a stationary point of `(N_r)` with multiplier `y∗`
(`∇_R L(R∗, y∗) = 0`) and `S∗ = C − ∑ᵢ y∗ᵢ Aᵢ` is positive semidefinite, then `X∗ = R∗ R∗ᵀ` is
optimal for (1) and `(S∗, y∗)` is optimal for (3). -/
theorem prop_2_4_stationary_psd_optimal {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) (hsa : StandingAssumptions C A b) {r : ℕ} (hr0 : 0 < r)
    (hrn : r ≤ n) (R : Matrix (Fin n) (Fin r) ℝ) (y : Fin m → ℝ)
    (hstat : IsStationary C A b R y) (hS : (slack C A y).PosSemidef) :
    IsPrimalOptimal C A b (R * Rᵀ) ∧ IsDualOptimal C A b (slack C A y) y := by sorry

end BurerMonteiro.RankIncrease
