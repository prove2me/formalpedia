-- Prove2me | Theorems.Thm_CentralityGame_lemma_1
-- name    : CentralityGame.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:06.174874+00:00
-- url     : https://prove2.me/theorems/90381627-66cf-4155-9f31-125f1a976224
-- title:
--   Lemma 1 — PageRank through hitting times (corrected: η positive)
-- statement:
--   Let $\mathcal G$ be a graph, $\beta\in(0,1)$ and $\eta$ an intrinsic centrality. For every node $i$, the PageRank centrality is given by
--
--   $$
--   \pi_i=\frac{1}{1+(1-\beta)\tau^i_\eta+\frac{\beta}{d_i}\sum_{j\in\mathcal N_i}\tau^i_j},\qquad\tau^i_\eta=\sum_{j\in\mathcal V}\eta_j\tau^i_j.
--   $$
--
--   Since the hitting times of $i$ do not depend on the out-links of $i$, only the last sum depends on the action of player $i$. This reduces best responses to a comparison of hitting times.
--
--   Differences from the source:
--   - correction: η a probability vector in ℝ^V_+, entries read as nonnegative → IsIntrinsicCentrality η: η_k > 0 for every k and ∑ η_k = 1; reason: with zero entries the statement fails: V = {1,2,3,4}, d ≡ 1, β = 1/2, x_2 = {1}, x_3 = {4}, x_4 = {3}, η = δ_3 keeps the walk in {3,4}, so π_1 = 0 for every action of player 1, the system (4) has no finite solution (τ^1_3 = ∞), and B_1 depends on η; the page itself calls P irreducible, which for every graph needs all η_k > 0
--   - encoding: graph G = (V, E) without self-loops or sinks → N : V → Finset V with IsGraph N; reason: (i, j) ∈ E iff j ∈ N i and d_i = (N i).card; the same graphs
--   - encoding: τ^i_j = E[T_i : V_0 = j] → hittingTime, the tail sum ∑_{t ≥ 0} P_j{T_i > t} of the published MarkovMixing.expSetHitTime at {i}; reason: the tail formula for the mean of a nonnegative integer variable; the tails decay geometrically for positive η, so the sum is the true expectation
--   - encoding: (I − βRᵀ)⁻¹ → Mathlib's matrix inverse; reason: I − βRᵀ is strictly diagonally dominant for a graph and β ∈ (0,1), so the inverse is the true one
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, Lemma 1, (5), p.7

import Mathlib
import Definitions.Def_CentralityGame_IsGraph
import Definitions.Def_CentralityGame_IsIntrinsicCentrality
import Definitions.Def_CentralityGame_pageRank
import Definitions.Def_CentralityGame_meanHittingTime

namespace CentralityGame

/-- Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, Lemma 1, (5), p.7: the PageRank centrality is given by
`π_i = 1 / (1 + (1 - β) τ^i_η + (β / d_i) ∑_{j ∈ N_i} τ^i_j)` for every node `i`.

**Formalization Note** `η` is positive, see `IsIntrinsicCentrality`. -/
theorem lemma_1 {V : Type*} [Fintype V] [DecidableEq V] (N : V → Finset V) (hN : IsGraph N) (β : ℝ)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (η : V → ℝ) (hη : IsIntrinsicCentrality η) (i : V) :
    pageRank N β η i =
      1 / (1 + (1 - β) * meanHittingTime N β η i +
        β / ((N i).card : ℝ) * ∑ j ∈ N i, hittingTime N β η i j) := by sorry

end CentralityGame
