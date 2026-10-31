-- Prove2me | Theorems.Thm_CentralityGame_eq_4
-- name    : CentralityGame.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:00.754617+00:00
-- url     : https://prove2.me/theorems/4aadbeb0-c06e-4eed-a800-af0bf1ce4a38
-- title:
--   §2, (4), p.7 — expected hitting times are the unique solution of the first-step system (corrected: η positive)
-- statement:
--   Let $\mathcal G$ be a graph, $\beta\in(0,1)$ and $\eta$ an intrinsic centrality. For every node $i$, the vector $(\tau^i_j)_{j\in\mathcal V}$ of expected hitting times of the chain $P=\beta R+(1-\beta)\mathbf 1\eta^\top$ is the unique solution of the linear system
--
--   $$
--   \tau^i_i=0,\qquad\tau^i_j=1+(1-\beta)\sum_{k\in\mathcal V}\eta_k\tau^i_k+\frac{\beta}{d_j}\sum_{k\in\mathcal N_j}\tau^i_k,\quad\forall j\ne i.
--   $$
--
--   Both halves are asserted: the hitting times solve the system, and any real vector solving it equals them. This links the probabilistic definition to the linear equations from which every later result is derived. The source cites Norris, *Markov Chains*, Theorem 1.3.5.
--
--   Differences from the source:
--   - correction: η a probability vector in ℝ^V_+, entries read as nonnegative → IsIntrinsicCentrality η: η_k > 0 for every k and ∑ η_k = 1; reason: with zero entries the statement fails: V = {1,2,3,4}, d ≡ 1, β = 1/2, x_2 = {1}, x_3 = {4}, x_4 = {3}, η = δ_3 keeps the walk in {3,4}, so π_1 = 0 for every action of player 1, the system (4) has no finite solution (τ^1_3 = ∞), and B_1 depends on η; the page itself calls P irreducible, which for every graph needs all η_k > 0
--   - encoding: graph G = (V, E) without self-loops or sinks → N : V → Finset V with IsGraph N; reason: (i, j) ∈ E iff j ∈ N i and d_i = (N i).card; the same graphs
--   - encoding: τ^i_j = E[T_i : V_0 = j] → hittingTime, the tail sum ∑_{t ≥ 0} P_j{T_i > t} of the published MarkovMixing.expSetHitTime at {i}; reason: the tail formula for the mean of a nonnegative integer variable; the tails decay geometrically for positive η, so the sum is the true expectation
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, (4), p.7

import Mathlib
import Definitions.Def_CentralityGame_IsGraph
import Definitions.Def_CentralityGame_IsIntrinsicCentrality
import Definitions.Def_CentralityGame_hittingTime

namespace CentralityGame

/-- The first-step system: Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, (4), p.7. For every `i`, the vector
`(τ^i_j)_{j ∈ V}` of expected hitting times is the unique solution of
`τ^i_i = 0`, `τ^i_j = 1 + (1 - β) ∑_{k ∈ V} η_k τ^i_k + (β / d_j) ∑_{k ∈ N_j} τ^i_k` for `j ≠ i`.

**Formalization Note** The two conjuncts are the two halves: `τ^i` solves the system, and every
real solution equals `τ^i`. `η` is positive, see `IsIntrinsicCentrality`. -/
theorem eq_4 {V : Type*} [Fintype V] [DecidableEq V] (N : V → Finset V) (hN : IsGraph N) (β : ℝ)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (η : V → ℝ) (hη : IsIntrinsicCentrality η) (i : V) :
    (hittingTime N β η i i = 0 ∧
      ∀ j, j ≠ i → hittingTime N β η i j =
        1 + (1 - β) * ∑ k, η k * hittingTime N β η i k +
          β / ((N j).card : ℝ) * ∑ k ∈ N j, hittingTime N β η i k) ∧
    ∀ t : V → ℝ, t i = 0 →
      (∀ j, j ≠ i → t j = 1 + (1 - β) * ∑ k, η k * t k + β / ((N j).card : ℝ) * ∑ k ∈ N j, t k) →
      t = hittingTime N β η i := by sorry

end CentralityGame
