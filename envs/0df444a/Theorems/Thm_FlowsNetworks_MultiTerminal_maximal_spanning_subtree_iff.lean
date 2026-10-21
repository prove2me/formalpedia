-- Prove2me | Theorems.Thm_FlowsNetworks_MultiTerminal_maximal_spanning_subtree_iff
-- name    : FlowsNetworks.MultiTerminal.maximal_spanning_subtree_iff
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:02.880927+00:00
-- url     : https://prove2.me/theorems/31d2dacd-b498-46c3-bba9-9e57ed0def6a
-- title:
--   Chapter IV, Theorem 1.1 — the cycle criterion for a maximal spanning subtree
-- statement:
--   Let $G$ be a connected undirected graph on a finite node set $N$ whose arcs carry real lengths $a(x, y)$, and let $T$ be a spanning subtree of $G$. For an out-of-tree arc $\{x_1, x_k\}$ (an arc of $G$ not in $T$), let $x_1, x_2, \dots, x_k$ be the chain of in-tree arcs joining $x_1$ and $x_k$. Then $T$ is a maximal spanning subtree of $G$ (no spanning subtree of $G$ has larger total length) if and only if, for every out-of-tree arc $\{x_1, x_k\}$,
--   $$a(x_1, x_k) \le \min\,[a(x_1, x_2), a(x_2, x_3), \dots, a(x_{k-1}, x_k)]. \tag{1.1}$$
--
--   This is the optimality criterion for maximum-weight spanning trees, the tool by which Chapter IV builds a tree realizing a given flow function.
--
--   **Formalization Note** The chain of in-tree arcs is any path in $T$ from $x_1$ to $x_k$; in a tree it is unique. The minimum in (1.1) is expressed as "$a(x_1, x_k)$ is at most the length of every arc of that path".
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter IV, p. 5, Theorem 1.1 (with Eq. (1.1), p. 3)

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree

namespace FlowsNetworks.MultiTerminal

/-- Ford–Fulkerson, *Flows in Networks*, Chapter IV, Theorem 1.1 (p. 5). Let `G` be a connected
graph whose arcs carry real lengths `a(x, y)`, and let `T` be a spanning subtree of `G`. Then `T` is
maximal (no spanning subtree of `G` is longer) if and only if (1.1) holds for each out-of-tree arc:
for every arc `(x₁, x_k)` of `G` not in `T`,
`a(x₁, x_k) ≤ min [a(x₁, x₂), a(x₂, x₃), …, a(x_{k−1}, x_k)]` along the chain of in-tree arcs
joining `x₁` and `x_k`. -/
theorem maximal_spanning_subtree_iff {N : Type} [Fintype N] [DecidableEq N]
    (G T : SimpleGraph N) (hG : G.Connected) (a : Sym2 N → ℝ)
    (hT : IsSpanningSubtree G T) :
    IsMaximalSpanningSubtree G T a ↔ OutOfTreeCondition G T a := by sorry

end FlowsNetworks.MultiTerminal
