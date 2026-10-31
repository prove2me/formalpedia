-- Prove2me | Theorems.Thm_CentralityGame_proposition_3_iii
-- name    : CentralityGame.proposition_3_iii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:31.276+00:00
-- url     : https://prove2.me/theorems/52c14e3d-2683-4886-a5c8-efc000de52d0
-- title:
--   Proposition 3(iii) — nodes that cannot reach $i$ are tied at the top (corrected: η positive)
-- statement:
--   Let $\mathcal G$ be a graph, $\beta\in(0,1)$ and $\eta$ an intrinsic centrality. For every node $i$, for every $h,j$ in $\mathcal V\setminus\mathcal N_i^{-\infty}$ and every $k$ in $\mathcal N_i^{-\infty}$,
--
--   $$
--   \tau^i_h=\tau^i_j>\tau^i_k.
--   $$
--
--   All nodes that cannot reach $i$ share one expected hitting time, which is strictly larger than that of any node reaching $i$. Hence a best response prefers every node that reaches $i$.
--
--   Differences from the source:
--   - correction: η a probability vector in ℝ^V_+, entries read as nonnegative → IsIntrinsicCentrality η: η_k > 0 for every k and ∑ η_k = 1; reason: with zero entries the statement fails: V = {1,2,3,4}, d ≡ 1, β = 1/2, x_2 = {1}, x_3 = {4}, x_4 = {3}, η = δ_3 keeps the walk in {3,4}, so π_1 = 0 for every action of player 1, the system (4) has no finite solution (τ^1_3 = ∞), and B_1 depends on η; the page itself calls P irreducible, which for every graph needs all η_k > 0
--   - encoding: graph G = (V, E) without self-loops or sinks → N : V → Finset V with IsGraph N; reason: (i, j) ∈ E iff j ∈ N i and d_i = (N i).card; the same graphs
--   - encoding: τ^i_j = E[T_i : V_0 = j] → hittingTime, the tail sum ∑_{t ≥ 0} P_j{T_i > t} of the published MarkovMixing.expSetHitTime at {i}; reason: the tail formula for the mean of a nonnegative integer variable; the tails decay geometrically for positive η, so the sum is the true expectation
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, Proposition 3(iii), (14), p.14

import Mathlib
import Definitions.Def_CentralityGame_IsGraph
import Definitions.Def_CentralityGame_IsIntrinsicCentrality
import Definitions.Def_CentralityGame_hittingTime
import Definitions.Def_CentralityGame_reachSet

namespace CentralityGame

/-- Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, Proposition 3(iii), (14), p.14: for every `h, j` in `V ∖ N_i^{-∞}` and `k`
in `N_i^{-∞}`, `τ^i_h = τ^i_j > τ^i_k`. -/
theorem proposition_3_iii {V : Type*} [Fintype V] [DecidableEq V] (N : V → Finset V)
    (hN : IsGraph N) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (η : V → ℝ)
    (hη : IsIntrinsicCentrality η) (i h j k : V) (hh : h ∉ reachSet N i) (hj : j ∉ reachSet N i)
    (hk : k ∈ reachSet N i) :
    hittingTime N β η i h = hittingTime N β η i j ∧
      hittingTime N β η i k < hittingTime N β η i j := by sorry

end CentralityGame
