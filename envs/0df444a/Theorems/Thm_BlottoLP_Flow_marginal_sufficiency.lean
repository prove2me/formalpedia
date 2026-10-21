-- Prove2me | Theorems.Thm_BlottoLP_Flow_marginal_sufficiency
-- name    : BlottoLP.Flow.marginal_sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:53.060977+00:00
-- url     : https://prove2.me/theorems/7154e271-229c-44c6-aa0a-9930a603a54e
-- title:
--   §3, p. 5 — the marginals of both players' strategies determine the expected payoff
-- statement:
--   Let $\sigma$ and $\tau$ be weight functions on the pure strategies of players A and B in an instance of Colonel Blotto, and let $\hat x_{k,l}=\sum_{x:\,x_k=l}\sigma(x)$ and $\hat y_{k,m}=\sum_{y:\,y_k=m}\tau(y)$ be their marginals. Then player A's expected payoff depends on $\sigma,\tau$ only through the marginals:
--   $$
--   \sum_{x}\sum_{y}\sigma(x)\,\tau(y)\,U(x,y)=\sum_{k=1}^{K}\sum_{l=0}^{A}\sum_{m=0}^{B}\hat x_{k,l}\,\hat y_{k,m}\,U_k(l,m).
--   $$
--
--   This is the "key observation" behind the marginal representation of Ahmadinejad et al.: the representations of both strategies suffice to determine the outcome of the game. It is what allows Linear Program 1 to express the payoff constraints in the marginal variables $P^A_{k,j}$.
--
--   **Formalization Note** The identity is stated for arbitrary real weight functions (it is bilinear and needs no normalization); in particular it holds for mixed strategies. It uses that the payoff on battlefield $k$ depends only on the troops placed there.
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), p. 5, §3 ("given the corresponding representations of the strategies of both players, one can determine the outcome of the game"), used through eq. (4) p. 9

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model

namespace BlottoLP.Flow

/-- §3, p. 5: the marginals of the two players' strategies determine the outcome of the game.
Player A's expected payoff is a function of the marginals alone. -/
theorem marginal_sufficiency (I : Instance) (σ : Pure I.K I.A → ℝ) (τ : Pure I.K I.B → ℝ) :
    expPayoff I σ τ =
      ∑ k, ∑ l : Fin (I.A + 1), ∑ m : Fin (I.B + 1),
        marginal σ (k, l) * marginal τ (k, m) * I.U k l m := by sorry

end BlottoLP.Flow
