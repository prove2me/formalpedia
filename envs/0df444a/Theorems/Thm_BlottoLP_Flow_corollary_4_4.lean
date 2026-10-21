-- Prove2me | Theorems.Thm_BlottoLP_Flow_corollary_4_4
-- name    : BlottoLP.Flow.corollary_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:48.994979+00:00
-- url     : https://prove2.me/theorems/3c674fc5-fe2f-4e23-a725-af865e8de9a7
-- title:
--   Corollary 4.4, p. 8 — the flow of a mixed strategy is a unit flow from v_{0,0} to v_{K,N}, with the strategy's marginals
-- statement:
--   Let $\sigma$ be a mixed strategy of a player with $N$ troops on $K$ battlefields, and let $F_\sigma$ be its flow: the edge $v_{k-1,i}\to v_{k,j}$ carries $\Pr_\sigma[s_{k-1}=i,\ s_k=j]$, where $s_k$ is the number of troops on the first $k$ battlefields. Then
--
--   1. $F_\sigma$ is a flow of size $1$ from $v_{0,0}$ to $v_{K,N}$ in the layered graph, i.e. it satisfies the membership constraints (a) of Linear Program 1;
--   2. eq. (3) applied to $F_\sigma$ returns the marginals of $\sigma$:
--   $$
--   \sum_{i=0}^{N-j}F_{\sigma}(v_{k-1,i}\to v_{k,i+j})=\Pr_\sigma[x_k=j]\qquad(1\le k\le K,\ 0\le j\le N).
--   $$
--
--   The corollary is what makes the flow variables of Linear Program 1 a valid encoding of A's mixed strategies, and the second part is the link between the flow variables and the marginals $P^A_{k,j}$ that the LP uses.
--
--   **Formalization Note** The paper's "exactly one corresponding flow" is the function $\sigma\mapsto F_\sigma$; the second conclusion makes explicit the use of eq. (3) on p. 9.
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), p. 8, Corollary 4.4, with eq. (3) p. 9

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model

namespace BlottoLP.Flow

/-- Corollary 4.4, with the link to eq. (3): the flow of a mixed strategy is a flow of size `1`
from `v_{0,0}` to `v_{K,N}` (the constraints (a) of Linear Program 1), and eq. (3) applied to it
returns the strategy's marginals. -/
theorem corollary_4_4 (K N : ℕ) (σ : Pure K N → ℝ) (hσ : IsMixed σ) :
    IsUnitFlow (flowOf σ) ∧ flowMarginal (flowOf σ) = marginal σ := by sorry

end BlottoLP.Flow
