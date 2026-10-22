-- Prove2me | Theorems.Thm_FlowsNetworks_MultiTerminal_condensed_flow_value
-- name    : FlowsNetworks.MultiTerminal.condensed_flow_value
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:13.361081+00:00
-- url     : https://prove2.me/theorems/12252cd8-2f3b-428d-b5bf-50e04362ec66
-- title:
--   Chapter IV, Lemma 3.1 — condensing one side of a minimal cut preserves maximal flow values
-- statement:
--   Let $G$ be an undirected network on a finite node set $N$ with nonnegative capacities, let $s \neq t$ be two nodes, and let $(X, \bar X)$ be a minimal cut separating $s$ and $t$, with $s \in X$ and $t \in \bar X$. Form the **condensed network** by shrinking all nodes of $\bar X$ to a single node, to which all arcs of the cut are attached; several arcs joining an ordinary node $x \in X$ to $\bar X$ are replaced by one arc whose capacity is the sum of theirs. Then for any two distinct ordinary nodes $x, y \in X$, the maximal flow value $v'(x, y)$ in the condensed network equals the maximal flow value $v(x, y)$ in $G$:
--   $$v'(x, y) = v(x, y).$$
--
--   This lemma is the step that lets the Gomory–Hu procedure solve each of its $n - 1$ maximal flow problems on a smaller, condensed network.
--
--   **Formalization Note** The equality is stated as: a real number $w$ is the maximal flow value from $x$ to $y$ in the condensed network if and only if it is the maximal flow value from $x$ to $y$ in $G$. The condensed network has node set `Option X`, with `none` the condensed node. The case where $x$ and $y$ both lie in $\bar X$ is the same lemma with the roles of $s$ and $t$ exchanged.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter IV, p. 11, Lemma 3.1 (with the condensed network of p. 10)

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_UndirectedNetwork

namespace FlowsNetworks.MultiTerminal

/-- Ford–Fulkerson, *Flows in Networks*, Chapter IV, Lemma 3.1 (p. 11). Let `(X, X̄)` be a minimal
cut separating the distinct nodes `s ∈ X` and `t ∈ X̄` in an undirected network `G`, and condense all
nodes of `X̄` into a single node. For two distinct ordinary nodes `x, y ∈ X`, the maximal flow value
`v′(x, y)` in the condensed network equals the maximal flow value `v(x, y)` in `G`: a number `w` is
the maximal flow value from `x` to `y` in the condensed network if and only if it is the maximal
flow value from `x` to `y` in `G`. -/
theorem condensed_flow_value {N : Type} [Fintype N] [DecidableEq N]
    (G : UNetwork N) (s t : N) (hst : s ≠ t) (X : Finset N) (hX : IsMinCut G s t X)
    (x y : N) (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) (w : ℝ) :
    IsMaxFlowValue (condense G X) (some ⟨x, hx⟩) (some ⟨y, hy⟩) w ↔
      IsMaxFlowValue G x y w := by sorry

end FlowsNetworks.MultiTerminal
