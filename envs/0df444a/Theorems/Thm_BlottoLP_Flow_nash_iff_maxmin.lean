-- Prove2me | Theorems.Thm_BlottoLP_Flow_nash_iff_maxmin
-- name    : BlottoLP.Flow.nash_iff_maxmin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:12.175204+00:00
-- url     : https://prove2.me/theorems/42329c1a-3212-4d9b-a5d0-c9c82a1f578c
-- title:
--   §3, p. 5 — in a zero-sum game, Nash equilibria are exactly the pairs of maxmin and minmax strategies
-- statement:
--   Let $M:\alpha\times\beta\to\mathbb R$ be a finite two-player zero-sum game (row player's payoff $M$, column player's $-M$). Then:
--
--   1. for all weight functions $\sigma$ on $\alpha$ and $\tau$ on $\beta$, $(\sigma,\tau)$ is a Nash equilibrium if and only if $\sigma$ is a maxmin strategy of the row player and $\tau$ is a minmax strategy of the column player;
--   2. consequently the row player's equilibrium strategies are exactly her maxmin strategies:
--   $$
--   \sigma\in R \iff \sigma \text{ is a maxmin strategy}.
--   $$
--
--   Applied to Colonel Blotto, this identifies $R_A$ (and hence $\mathcal P_A$) with the set of strategies that Linear Program 1 optimizes: a strategy of A is in a Nash equilibrium exactly when it guarantees the game value.
--
--   **Formalization Note** The statement is for any finite zero-sum game, of which Colonel Blotto (with $M=U$ on the allocation sets) is an instance. It contains von Neumann's minimax theorem (if one strategy set is empty, both sides of each equivalence are false). The levels of maxmin and minmax strategies are explicit witnesses $v$, not suprema or infima.
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), p. 5, §3 ("the game is in Nash Equilibrium if and only if both players play a maxmin strategy")

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum

namespace BlottoLP.Flow

/-- §3, p. 5: in a finite two-player zero-sum game, `(σ, τ)` is a Nash equilibrium if and only if
`σ` is a maxmin strategy and `τ` a minmax strategy; consequently the strategies of the row player
that occur in a Nash equilibrium are exactly her maxmin strategies. -/
theorem nash_iff_maxmin {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℝ) :
    (∀ (σ : α → ℝ) (τ : β → ℝ), IsNashEq M σ τ ↔ IsMaxmin M σ ∧ IsMinmax M τ) ∧
    (∀ σ : α → ℝ, σ ∈ nashRow M ↔ IsMaxmin M σ) := by sorry

end BlottoLP.Flow
