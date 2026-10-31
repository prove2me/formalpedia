-- Prove2me | Theorems.Thm_CentralityGame_proposition_3_i
-- name    : CentralityGame.proposition_3_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:32.915988+00:00
-- url     : https://prove2.me/theorems/f7025415-20f5-4d97-a461-76aca8c02c82
-- title:
--   Proposition 3(i) — the relative order of the hitting times does not depend on η (corrected: η positive)
-- statement:
--   Let $\mathcal G$ be a graph and $\beta\in(0,1)$. For every node $i$, the relative order of $\{\tau^i_j:j\in\mathcal V\}$ does not depend on the intrinsic centrality: for any two intrinsic centralities $\eta,\eta'$ and all nodes $j,k$,
--
--   $$
--   \tau^{i,\eta}_j\le\tau^{i,\eta}_k\iff\tau^{i,\eta'}_j\le\tau^{i,\eta'}_k,
--   $$
--
--   where $\tau^{i,\eta}$ denotes the hitting times of the chain with intrinsic centrality $\eta$. The individual values do depend on $\eta$; their order does not. With Proposition 2 this gives independence of the best response from $\eta$.
--
--   Differences from the source:
--   - correction: η a probability vector in ℝ^V_+, entries read as nonnegative → IsIntrinsicCentrality η: η_k > 0 for every k and ∑ η_k = 1; reason: with zero entries the statement fails: V = {1,2,3,4}, d ≡ 1, β = 1/2, x_2 = {1}, x_3 = {4}, x_4 = {3}, η = δ_3 keeps the walk in {3,4}, so π_1 = 0 for every action of player 1, the system (4) has no finite solution (τ^1_3 = ∞), and B_1 depends on η; the page itself calls P irreducible, which for every graph needs all η_k > 0
--   - encoding: graph G = (V, E) without self-loops or sinks → N : V → Finset V with IsGraph N; reason: (i, j) ∈ E iff j ∈ N i and d_i = (N i).card; the same graphs
--   - encoding: τ^i_j = E[T_i : V_0 = j] → hittingTime, the tail sum ∑_{t ≥ 0} P_j{T_i > t} of the published MarkovMixing.expSetHitTime at {i}; reason: the tail formula for the mean of a nonnegative integer variable; the tails decay geometrically for positive η, so the sum is the true expectation
--   - encoding: the relative order does not depend on η → for all positive η, η′ and all j, k: τ^η_j ≤ τ^η_k ↔ τ^η′_j ≤ τ^η′_k; reason: the ≤ relation for both orderings of (j, k) determines strict order and ties
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, Proposition 3(i), p.14

import Mathlib
import Definitions.Def_CentralityGame_IsGraph
import Definitions.Def_CentralityGame_IsIntrinsicCentrality
import Definitions.Def_CentralityGame_hittingTime

namespace CentralityGame

/-- Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, Proposition 3(i), p.14: for every `i`, the relative order of
`{τ^i_j : j ∈ V}` does not depend on `η`.

**Formalization Note** "Does not depend on `η`" is the comparison of two arbitrary positive
`η, η'` at the same graph and the same `β`. Applied in both directions, the `≤` form also gives
the strict order and ties. -/
theorem proposition_3_i {V : Type*} [Fintype V] [DecidableEq V] (N : V → Finset V) (hN : IsGraph N)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (η η' : V → ℝ) (hη : IsIntrinsicCentrality η)
    (hη' : IsIntrinsicCentrality η') (i j k : V) :
    hittingTime N β η i j ≤ hittingTime N β η i k ↔
      hittingTime N β η' i j ≤ hittingTime N β η' i k := by sorry

end CentralityGame
