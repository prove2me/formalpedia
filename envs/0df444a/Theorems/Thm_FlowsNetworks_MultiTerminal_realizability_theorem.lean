-- Prove2me | Theorems.Thm_FlowsNetworks_MultiTerminal_realizability_theorem
-- name    : FlowsNetworks.MultiTerminal.realizability_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:13.272147+00:00
-- url     : https://prove2.me/theorems/390974b5-737a-4573-8d3f-a8e64c60853c
-- title:
--   Chapter IV, Theorem 2.1 — flow functions are exactly the functions satisfying (2.1), and are realizable by trees
-- statement:
--   Let $N$ be a nonempty finite set of nodes, and let $v$ be a symmetric function on pairs of distinct nodes, $v(x, y) = v(y, x) \ge 0$. Call $v$ **realizable** if there is an undirected network on $N$, with nonnegative arc capacities, whose flow function is $v$, i.e. $v(x, y)$ is the maximal flow value from $x$ to $y$ for all $x \neq y$. Then:
--
--   1. $v$ is realizable if and only if for all pairwise distinct nodes $x, y, z$
--   $$v(x, y) \ge \min\,[v(x, z), v(z, y)]. \tag{2.1}$$
--   2. If $v$ is realizable, it is realizable by a tree: there is an undirected network on $N$ whose arcs form a tree (a connected graph without cycles on all of $N$) and whose flow function is $v$.
--
--   This is the Gomory–Hu characterization of the maximal-flow values between all pairs of nodes of an undirected network: a single tree carries the same all-pairs flow values as any network, and only $n - 1$ distinct values can occur.
--
--   **Formalization Note** The hypothesis $v \ge 0$ is not printed in the theorem; it is the book's implicit reading (flow values are maximal flow values, capacities nonnegative reals, Chapter I, p. 7), and without it the "if" direction is false ($v \equiv -1$, finding F1). Diagonal values $v(x, x)$ are undefined in the book and unconstrained here; (2.1) is quantified over pairwise distinct nodes. The node set is assumed nonempty because a tree is connected and so has at least one node. In the realizing tree some arcs may have capacity $0$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter IV, p. 8, Theorem 2.1

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_UndirectedNetwork

namespace FlowsNetworks.MultiTerminal

/-- Ford–Fulkerson, *Flows in Networks*, Chapter IV, Theorem 2.1 (p. 8). Let `v` be a symmetric
function on pairs of distinct nodes of a nonempty finite node set `N`, with nonnegative values.
Then `v` is realizable as the flow function of an undirected network on `N` if and only if `v`
satisfies (2.1) `v(x, y) ≥ min [v(x, z), v(z, y)]` for all pairwise distinct `x, y, z`. If `v` is
realizable, it is realizable by a tree: by an undirected network whose arcs form a tree on `N`. -/
theorem realizability_theorem {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
    (v : N → N → ℝ)
    (hsymm : ∀ x y : N, x ≠ y → v x y = v y x)
    (hnonneg : ∀ x y : N, x ≠ y → 0 ≤ v x y) :
    ((∃ G : UNetwork N, IsFlowFunction G v) ↔
        ∀ x y z : N, x ≠ y → x ≠ z → z ≠ y → v x y ≥ min (v x z) (v z y)) ∧
      ((∃ G : UNetwork N, IsFlowFunction G v) →
        ∃ T : UNetwork N, T.graph.IsTree ∧ IsFlowFunction T v) := by sorry

end FlowsNetworks.MultiTerminal
