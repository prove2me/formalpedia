-- Prove2me | Theorems.Thm_CentralityGame_proposition_2
-- name    : CentralityGame.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:44.983568+00:00
-- url     : https://prove2.me/theorems/10a7678b-9f5a-4995-b180-04c171cc706a
-- title:
--   Proposition 2 — best responses are the actions with the smallest hitting times (corrected: η positive, k ≠ i)
-- statement:
--   Consider a centrality game with out-degree profile $\mathbf d$, discount factor $\beta\in(0,1)$ and intrinsic centrality $\eta$. For every player $i$ and every configuration $x$, with hitting times taken in $\mathcal G(x)$,
--
--   $$
--   x_i\in\mathcal B_i(x_{-i})\iff\tau^i_k(x_{-i})\ge\max_{j\in x_i}\tau^i_j(x_{-i}),\quad\forall k\notin x_i,\ k\ne i.
--   $$
--
--   So computing a best response amounts to finding $d_i$ nodes with the smallest expected hitting times of $i$.
--
--   Differences from the source:
--   - correction: (13) quantifies over all k ∉ x_i → over k ∉ x_i with k ≠ i; reason: k = i satisfies k ∉ x_i and τ^i_i = 0 < τ^i_j for j ∈ x_i (τ^i_j ≥ 1), so the printed right side is always false while best responses exist, e.g. the three-node ring with d ≡ 1; the page's proof chooses nodes in V∖{i}
--   - correction: η a probability vector in ℝ^V_+, entries read as nonnegative → IsIntrinsicCentrality η: η_k > 0 for every k and ∑ η_k = 1; reason: with zero entries the statement fails: V = {1,2,3,4}, d ≡ 1, β = 1/2, x_2 = {1}, x_3 = {4}, x_4 = {3}, η = δ_3 keeps the walk in {3,4}, so π_1 = 0 for every action of player 1, the system (4) has no finite solution (τ^1_3 = ∞), and B_1 depends on η; the page itself calls P irreducible, which for every graph needs all η_k > 0
--   - encoding: τ^i_j = E[T_i : V_0 = j] → hittingTime, the tail sum ∑_{t ≥ 0} P_j{T_i > t} of the published MarkovMixing.expSetHitTime at {i}; reason: the tail formula for the mean of a nonnegative integer variable; the tails decay geometrically for positive η, so the sum is the true expectation
--   - encoding: x_{−i} ∈ X_{−i} and objects of G(x) written as functions of x_{−i} → a full configuration x, with N_i^{−l}, N_i^{−∞} and τ^i computed in G(x) and B_i via Function.update x i; reason: these objects do not depend on x_i (p.13), and x is arbitrary, so every x_{−i} and every action x_i is covered
--   - encoding: τ^i_k ≥ max_{j∈x_i} τ^i_j → ∀ j ∈ x i, τ^i_j ≤ τ^i_k; reason: x_i is nonempty and finite, so the two are the same
--   - encoding: (I − βRᵀ)⁻¹ → Mathlib's matrix inverse; reason: I − βRᵀ is strictly diagonally dominant for a graph and β ∈ (0,1), so the inverse is the true one
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, Proposition 2, (13), p.14

import Mathlib
import Definitions.Def_CentralityGame_IsOutDegreeProfile
import Definitions.Def_CentralityGame_IsConfiguration
import Definitions.Def_CentralityGame_IsIntrinsicCentrality
import Definitions.Def_CentralityGame_hittingTime
import Definitions.Def_CentralityGame_bestResponse

namespace CentralityGame

/-- Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, Proposition 2, (13), p.14, **corrected**: in a centrality game, `x_i` is a
best response iff `τ^i_k ≥ max_{j ∈ x_i} τ^i_j` for every `k ∉ x_i` with `k ≠ i`.

**Formalization Note** The page quantifies over all `k ∉ x_i`, which includes `k = i`, where
`τ^i_i = 0` makes the right side false; the page's proof picks nodes in `V ∖ {i}`. The `max` is
written `∀ j ∈ x i`. `η` is positive, see `IsIntrinsicCentrality`. -/
theorem proposition_2 {V : Type*} [Fintype V] [DecidableEq V] (d : V → ℕ)
    (hd : IsOutDegreeProfile d) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (η : V → ℝ)
    (hη : IsIntrinsicCentrality η) (x : V → Finset V) (hx : IsConfiguration d x) (i : V) :
    x i ∈ bestResponse d β η x i ↔
      ∀ k, k ∉ x i → k ≠ i → ∀ j ∈ x i, hittingTime x β η i j ≤ hittingTime x β η i k := by sorry

end CentralityGame
