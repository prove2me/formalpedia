-- Prove2me | Theorems.Thm_BlottoLP_Flow_linear_program_1
-- name    : BlottoLP.Flow.linear_program_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:58.861248+00:00
-- url     : https://prove2.me/theorems/00fbd261-a8be-4e60-bda4-736d3fa7bf8c
-- title:
--   Linear Program 1, p. 10 (corrected) — 𝒫_A is the projection of the feasible set of LP1 at the game value
-- statement:
--   Let $(\sigma_0,\tau_0)$ be a Nash equilibrium of an instance of Colonel Blotto, with game value $v=U(\sigma_0,\tau_0)$ (player A's expected payoff). A vector $\hat x\in\mathbb R^{K\times(A+1)}$ belongs to $\mathcal P_A$ if and only if there are
--
--   1. flow variables $F$ on the layered graph $L^A$ satisfying the constraints (a) of Linear Program 1 (a flow of size $1$ from $v_{0,0}$ to $v_{K,A}$),
--   2. with $\hat x$ given by eq. (3): $\hat x_{k,j}=\sum_{i=0}^{A-j}F_{k,i,i+j}$, and
--   3. dynamic-programming variables $D$ on $L^B$ with
--   $$
--   D_{0,0}=0,\qquad D_{k,i}\ge D_{k-1,j}+W^B_{k,i-j}\ (0\le j\le i\le B),\qquad D_{K,B}\le -v,
--   $$
--   where $W^B_{k,i}=\sum_{l=0}^{A}\hat x_{k,l}\,U^B_k(i,l)$ is eq. (4).
--
--   So the Nash-equilibrium marginals of A are exactly the projections of the solutions of Linear Program 1 with $u$ at its optimal value $v$. This is the formulation whose size Theorem 4.6 counts.
--
--   **Formalization Note** The game value is taken from a given Nash equilibrium instead of as a supremum, which keeps junk values out; the hypothesis is satisfiable (an equilibrium exists in every instance with $K\ge1$). The row $D^B_{0,i}=0$ for all $i$ of the printed LP1 is corrected to $D_{0,0}=0$: with the printed row LP1 can certify a payoff below the game value (see the definition `Model`). $\mathcal P_A$ is defined from the Nash equilibria, independently of the LP.
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), p. 10, Linear Program 1 (corrected), with eqs. (3)–(4) p. 9

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model

namespace BlottoLP.Flow

/-- Linear Program 1, p. 10 (corrected), at its optimal value: given a Nash equilibrium
`(σ₀, τ₀)`, with game value `v = expPayoff I σ₀ τ₀`, a vector `x̂` lies in `𝒫_A` if and only if
there are flow variables `F` satisfying the constraints (a), with `x̂` given by eq. (3), and
dynamic-programming variables `D` satisfying the rows of (b) for the weights (4) of `x̂`, with
`D_{K,B} ≤ -v`. -/
theorem linear_program_1 (I : Instance) (σ₀ : Pure I.K I.A → ℝ) (τ₀ : Pure I.K I.B → ℝ)
    (h : IsNashEq (payoff I) σ₀ τ₀) (xhat : Fin I.K × Fin (I.A + 1) → ℝ) :
    xhat ∈ PA I ↔
      ∃ (F : Edge I.K I.A → ℝ) (D : Fin (I.K + 1) → Fin (I.B + 1) → ℝ),
        IsUnitFlow F ∧ flowMarginal F = xhat ∧ IsDPBound (weightB I xhat) D ∧
          D (Fin.last I.K) (Fin.last I.B) ≤ - expPayoff I σ₀ τ₀ := by sorry

end BlottoLP.Flow
