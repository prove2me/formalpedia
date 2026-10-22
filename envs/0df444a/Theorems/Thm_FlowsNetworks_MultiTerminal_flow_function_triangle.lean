-- Prove2me | Theorems.Thm_FlowsNetworks_MultiTerminal_flow_function_triangle
-- name    : FlowsNetworks.MultiTerminal.flow_function_triangle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:11.169282+00:00
-- url     : https://prove2.me/theorems/42e259ab-49d0-4eff-ac1c-63c12d5e3029
-- title:
--   Chapter IV, Lemma 2.1 — the flow function satisfies the triangle condition (2.1)
-- statement:
--   Let $G$ be an undirected network on a finite node set $N$ with nonnegative arc capacities, and let $v$ be its flow function: $v(x, y)$ is the maximal flow value from $x$ to $y$ for distinct nodes $x \neq y$. Then for all pairwise distinct nodes $x, y, z$,
--   $$v(x, y) \ge \min\,[v(x, z), v(z, y)]. \tag{2.1}$$
--
--   This "triangle" inequality is the necessary condition in the characterization of flow functions (Theorem 2.1).
--
--   **Formalization Note** The book leaves $v(x, x)$ undefined (and remarks that setting $v(x, x) = \infty$ makes distinctness unnecessary), so the nodes are quantified pairwise distinct.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter IV, p. 6, Lemma 2.1, Eq. (2.1)

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_UndirectedNetwork

namespace FlowsNetworks.MultiTerminal

/-- Ford–Fulkerson, *Flows in Networks*, Chapter IV, Lemma 2.1 (p. 6). If `v` is the flow function
of an undirected network `G`, then for all nodes `x, y, z` (pairwise distinct, since `v(x, x)` is
undefined), (2.1) `v(x, y) ≥ min [v(x, z), v(z, y)]`. -/
theorem flow_function_triangle {N : Type} [Fintype N] [DecidableEq N]
    (G : UNetwork N) (v : N → N → ℝ) (hv : IsFlowFunction G v)
    (x y z : N) (hxy : x ≠ y) (hxz : x ≠ z) (hzy : z ≠ y) :
    v x y ≥ min (v x z) (v z y) := by sorry

end FlowsNetworks.MultiTerminal
