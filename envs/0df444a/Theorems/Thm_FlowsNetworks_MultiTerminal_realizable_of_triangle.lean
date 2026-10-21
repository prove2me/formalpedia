-- Prove2me | Theorems.Thm_FlowsNetworks_MultiTerminal_realizable_of_triangle
-- name    : FlowsNetworks.MultiTerminal.realizable_of_triangle
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:10.939751+00:00
-- url     : https://prove2.me/theorems/da667a82-600f-45e0-a6fe-effd34bd7807
-- title:
--   Chapter IV, Lemma 2.2 — every symmetric function satisfying (2.1) is a flow function
-- statement:
--   Let $N$ be a finite set and $v$ a symmetric function defined on pairs of distinct elements of $N$, $v(x, y) = v(y, x)$, with nonnegative values. Suppose that for all pairwise distinct $x, y, z \in N$,
--   $$v(x, y) \ge \min\,[v(x, z), v(z, y)]. \tag{2.1}$$
--   Then there is an undirected network on the node set $N$ (nonnegative capacities) whose flow function is $v$: for all distinct $x, y$, the maximal flow value from $x$ to $y$ is $v(x, y)$.
--
--   This is the sufficiency half of the characterization of flow functions (Theorem 2.1).
--
--   **Formalization Note** The hypothesis $v \ge 0$ is not printed in the lemma; it is the book's implicit reading (a flow function's values are maximal flow values and capacities are nonnegative reals, Chapter I, p. 7). Without it the statement is false: $v \equiv -1$ satisfies (2.1) but is not a flow function (finding F1). Diagonal values $v(x, x)$ are undefined in the book and play no role.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter IV, p. 8, Lemma 2.2

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_UndirectedNetwork

namespace FlowsNetworks.MultiTerminal

/-- Ford–Fulkerson, *Flows in Networks*, Chapter IV, Lemma 2.2 (p. 8). If the symmetric function
`v` (defined for pairs of distinct nodes, with nonnegative values, as every maximal flow value is)
satisfies (2.1) `v(x, y) ≥ min [v(x, z), v(z, y)]` for all pairwise distinct `x, y, z`, there is an
undirected network on the same nodes having flow function `v`. -/
theorem realizable_of_triangle {N : Type} [Fintype N] [DecidableEq N]
    (v : N → N → ℝ)
    (hsymm : ∀ x y : N, x ≠ y → v x y = v y x)
    (hnonneg : ∀ x y : N, x ≠ y → 0 ≤ v x y)
    (htri : ∀ x y z : N, x ≠ y → x ≠ z → z ≠ y → v x y ≥ min (v x z) (v z y)) :
    ∃ G : UNetwork N, IsFlowFunction G v := by sorry

end FlowsNetworks.MultiTerminal
