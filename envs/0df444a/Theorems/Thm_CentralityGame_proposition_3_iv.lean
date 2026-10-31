-- Prove2me | Theorems.Thm_CentralityGame_proposition_3_iv
-- name    : CentralityGame.proposition_3_iv
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:59.45699+00:00
-- url     : https://prove2.me/theorems/50a52f93-dcd8-4441-b46e-c7c57c25fd3b
-- title:
--   Proposition 3(iv) — a hitting time exceeds the minimum over any cut-set (corrected: η positive)
-- statement:
--   Let $\mathcal G$ be a graph, $\beta\in(0,1)$ and $\eta$ an intrinsic centrality. For every node $i$, every $k$ in $\mathcal N_i^{-\infty}$ with $k\ne i$ and every cut-set $\mathcal C\subseteq\mathcal V\setminus\{k,i\}$ between $k$ and $i$,
--
--   $$
--   \tau^i_k>\min_{j\in\mathcal C}\tau^i_j.
--   $$
--
--   Every route from $k$ to $i$ crosses $\mathcal C$, and some node of $\mathcal C$ is strictly closer to $i$ in expected time than $k$. This yields the path along which hitting times decrease in Theorem 1.
--
--   Differences from the source:
--   - correction: η a probability vector in ℝ^V_+, entries read as nonnegative → IsIntrinsicCentrality η: η_k > 0 for every k and ∑ η_k = 1; reason: with zero entries the statement fails: V = {1,2,3,4}, d ≡ 1, β = 1/2, x_2 = {1}, x_3 = {4}, x_4 = {3}, η = δ_3 keeps the walk in {3,4}, so π_1 = 0 for every action of player 1, the system (4) has no finite solution (τ^1_3 = ∞), and B_1 depends on η; the page itself calls P irreducible, which for every graph needs all η_k > 0
--   - encoding: graph G = (V, E) without self-loops or sinks → N : V → Finset V with IsGraph N; reason: (i, j) ∈ E iff j ∈ N i and d_i = (N i).card; the same graphs
--   - encoding: τ^i_j = E[T_i : V_0 = j] → hittingTime, the tail sum ∑_{t ≥ 0} P_j{T_i > t} of the published MarkovMixing.expSetHitTime at {i}; reason: the tail formula for the mean of a nonnegative integer variable; the tails decay geometrically for positive η, so the sum is the true expectation
--   - encoding: τ^i_k > min_{j∈C} τ^i_j → ∃ j ∈ C, τ^i_j < τ^i_k; reason: such a C is nonempty because k reaches i, so the two are the same
--   - encoding: k ∈ N_i^{−∞}, with k = i not excluded in the clause itself → k ≠ i is a conjunct of IsCutSet; reason: p.5 defines cut-sets only between two distinct nodes
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, Proposition 3(iv), (15), p.14

import Mathlib
import Definitions.Def_CentralityGame_IsGraph
import Definitions.Def_CentralityGame_IsIntrinsicCentrality
import Definitions.Def_CentralityGame_hittingTime
import Definitions.Def_CentralityGame_reachSet
import Definitions.Def_CentralityGame_IsCutSet

namespace CentralityGame

/-- Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, Proposition 3(iv), (15), p.14: for every `k` in `N_i^{-∞}` and cut-set
`C ⊆ V ∖ {k, i}` between `k` and `i`, `τ^i_k > min_{j ∈ C} τ^i_j`.

**Formalization Note** The `min` is written `∃ j ∈ C, τ^i_j < τ^i_k`, the same statement because
such a `C` is nonempty (`k` reaches `i`). `IsCutSet` carries `k ≠ i`, as cut-sets are defined
between distinct nodes only. -/
theorem proposition_3_iv {V : Type*} [Fintype V] [DecidableEq V] (N : V → Finset V)
    (hN : IsGraph N) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (η : V → ℝ)
    (hη : IsIntrinsicCentrality η) (i k : V) (hk : k ∈ reachSet N i) (C : Finset V)
    (hC : IsCutSet N k i C) :
    ∃ j ∈ C, hittingTime N β η i j < hittingTime N β η i k := by sorry

end CentralityGame
