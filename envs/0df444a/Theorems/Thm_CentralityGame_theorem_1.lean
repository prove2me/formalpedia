-- Prove2me | Theorems.Thm_CentralityGame_theorem_1
-- name    : CentralityGame.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:45.064169+00:00
-- url     : https://prove2.me/theorems/c93a8fef-7f3b-4c66-b64b-10f1fdeb3a40
-- title:
--   Theorem 1 — independence from η and locality of the best response (corrected: η positive)
-- statement:
--   Consider a centrality game with node set $\mathcal V$, out-degree profile $\mathbf d\in\{1,\dots,n-1\}^{\mathcal V}$ and discount factor $\beta\in(0,1)$. Each node $i$ picks a set $x_i$ of $d_i$ other nodes to link to, and its utility is its PageRank centrality in the resulting graph $\mathcal G(x)$. Then, for every player $i$ and every action profile $x_{-i}$:
--
--   1. The best response set $\mathcal B_i(x_{-i})$ does not depend on the intrinsic centrality $\eta$.
--   2. If $|\mathcal N_i^{-\infty}(x_{-i})|>d_i$, then
--   $$
--   x_i\in\mathcal B_i(x_{-i})\implies x_i\subseteq\mathcal N_i^{-d_i}(x_{-i})\setminus\{i\},
--   $$
--   and, for such a best response $x_i$, from every $j$ in $x_i$ there exists a path $(r_0,r_1,\dots,r_l)$ from $r_0=j$ to $r_l=i$ in $\mathcal G(x)$ such that $\{r_k:0\le k<l\}\subseteq x_i$ and
--   $$
--   \tau^i_j(x_{-i})=\tau^i_{r_0}(x_{-i})>\tau^i_{r_1}(x_{-i})>\dots>\tau^i_{r_l}(x_{-i})=\tau^i_i(x_{-i})=0.
--   $$
--   3. If $|\mathcal N_i^{-\infty}(x_{-i})|\le d_i$, then
--   $$
--   x_i\in\mathcal B_i(x_{-i})\iff x_i\supseteq\mathcal N_i^{-d_i}(x_{-i})\setminus\{i\}.
--   $$
--
--   Here $\eta$ ranges over intrinsic centralities, $\mathcal N_i^{-l}$ is the set of nodes with a walk of length at most $l$ to $i$, and $\tau^i_j$ is the expected hitting time of $i$ from $j$ under the PageRank chain of $\mathcal G(x)$.
--
--   The theorem says that the wiring a node should choose does not depend on $\eta$, and that a node gains nothing by linking to a node at incoming distance more than $d_i$ when enough nearer nodes exist.
--
--   Differences from the source:
--   - correction: η a probability vector in ℝ^V_+, entries read as nonnegative → IsIntrinsicCentrality η: η_k > 0 for every k and ∑ η_k = 1; reason: with zero entries the statement fails: V = {1,2,3,4}, d ≡ 1, β = 1/2, x_2 = {1}, x_3 = {4}, x_4 = {3}, η = δ_3 keeps the walk in {3,4}, so π_1 = 0 for every action of player 1, the system (4) has no finite solution (τ^1_3 = ∞), and B_1 depends on η; the page itself calls P irreducible, which for every graph needs all η_k > 0
--   - reading: the path clause of (ii) is printed after (20), with no explicit hypothesis → the clause is assumed under x_i ∈ B_i(x_{−i}) as well as |N_i^{−∞}| > d_i; reason: the page's proof starts "Let x_i in B_i(x_{−i}) be a best response action"; for a non-best action j ∈ x_i may not reach i at all, so the clause would be false
--   - reading: "{r_k : ≤ k < l} ⊆ x_i", a misprint with the lower bound missing → r_k ∈ x_i for every 0 ≤ k < l; reason: the page's proof writes "r_k ∈ x_i for 0 ≤ k < l"; since r_0 = j ∈ x_i this is the same as starting at k = 1
--   - encoding: x_{−i} ∈ X_{−i} and objects of G(x) written as functions of x_{−i} → a full configuration x, with N_i^{−l}, N_i^{−∞} and τ^i computed in G(x) and B_i via Function.update x i; reason: these objects do not depend on x_i (p.13), and x is arbitrary, so every x_{−i} and every action x_i is covered
--   - encoding: τ^i_j = E[T_i : V_0 = j] → hittingTime, the tail sum ∑_{t ≥ 0} P_j{T_i > t} of the published MarkovMixing.expSetHitTime at {i}; reason: the tail formula for the mean of a nonnegative integer variable; the tails decay geometrically for positive η, so the sum is the true expectation
--   - encoding: the chain (21) of equalities and strict inequalities → r 0 = j, r (Fin.last l) = i, τ strictly decreasing at each step, and τ^i_i = 0; reason: the equalities τ^i_j = τ^i_{r_0} and τ^i_{r_l} = τ^i_i follow from the endpoint equations
--   - encoding: a path as an (l+1)-tuple → r : Fin (l + 1) → V with IsPath x r; reason: the same tuples
--   - encoding: (I − βRᵀ)⁻¹ → Mathlib's matrix inverse; reason: I − βRᵀ is strictly diagonally dominant for a graph and β ∈ (0,1), so the inverse is the true one
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, Theorem 1, (20)–(22), p.16

import Mathlib
import Definitions.Def_CentralityGame_IsOutDegreeProfile
import Definitions.Def_CentralityGame_IsConfiguration
import Definitions.Def_CentralityGame_IsIntrinsicCentrality
import Definitions.Def_CentralityGame_IsPath
import Definitions.Def_CentralityGame_hittingTime
import Definitions.Def_CentralityGame_reachSet
import Definitions.Def_CentralityGame_bestResponse

namespace CentralityGame

/-- Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, Theorem 1, p.16 (independence from `η` and locality of the best response):
in a centrality game, for every player `i` and action profile `x_{-i}`,

(i) the best response set `B_i(x_{-i})` does not depend on the intrinsic centrality `η`;

(ii) if `|N_i^{-∞}(x_{-i})| > d_i`, a best response `x_i` satisfies
`x_i ⊆ N_i^{-d_i}(x_{-i}) ∖ {i}` (20), and from every `j` in `x_i` there is a path
`(r_0, …, r_l)` from `r_0 = j` to `r_l = i` in `G(x)` with `{r_k : 0 ≤ k < l} ⊆ x_i` and
`τ^i_j = τ^i_{r_0} > τ^i_{r_1} > ⋯ > τ^i_{r_l} = τ^i_i = 0` (21);

(iii) if `|N_i^{-∞}(x_{-i})| ≤ d_i`, then `x_i ∈ B_i(x_{-i})` iff `x_i ⊇ N_i^{-d_i}(x_{-i}) ∖ {i}` (22).

**Formalization Note** The sets `N_i^{-l}`, `N_i^{-∞}` and the `τ^i` are taken of `G(x)` for the full
configuration `x`; on the page they are functions of `x_{-i}`, and they do not change with `x_i`.
Since `x` is arbitrary, (ii) and (iii) cover every action `x_i`. `η` is positive, see
`IsIntrinsicCentrality`. The path clause of (ii) holds under `x_i ∈ B_i`, as in the page's proof. -/
theorem theorem_1 {V : Type*} [Fintype V] [DecidableEq V] (d : V → ℕ)
    (hd : IsOutDegreeProfile d) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (x : V → Finset V)
    (hx : IsConfiguration d x) (i : V) :
    (∀ η η' : V → ℝ, IsIntrinsicCentrality η → IsIntrinsicCentrality η' →
      bestResponse d β η x i = bestResponse d β η' x i) ∧
    (∀ η : V → ℝ, IsIntrinsicCentrality η → d i < (reachSet x i).card →
      x i ∈ bestResponse d β η x i →
        x i ⊆ (reachWithin x i (d i)).erase i ∧
        ∀ j ∈ x i, ∃ (l : ℕ) (r : Fin (l + 1) → V),
          IsPath x r ∧ r 0 = j ∧ r (Fin.last l) = i ∧
          (∀ k : Fin l, r k.castSucc ∈ x i) ∧
          (∀ k : Fin l,
            hittingTime x β η i (r k.succ) < hittingTime x β η i (r k.castSucc)) ∧
          hittingTime x β η i i = 0) ∧
    (∀ η : V → ℝ, IsIntrinsicCentrality η → (reachSet x i).card ≤ d i →
      (x i ∈ bestResponse d β η x i ↔ (reachWithin x i (d i)).erase i ⊆ x i)) := by sorry

end CentralityGame
