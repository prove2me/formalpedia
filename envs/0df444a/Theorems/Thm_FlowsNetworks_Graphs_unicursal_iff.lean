-- Prove2me | Theorems.Thm_FlowsNetworks_Graphs_unicursal_iff
-- name    : FlowsNetworks.Graphs.unicursal_iff
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:01.889059+00:00
-- url     : https://prove2.me/theorems/b405965f-0a1a-40a8-bcd7-14659b573a5d
-- title:
--   Chapter II, Theorem 7.1 — a mixed graph is unicursal iff it is connected, even, and cut-balanced
-- statement:
--   Let $G = [N; \mathcal A]$ be a finite **mixed graph**: each arc is either directed, an ordered pair $(x, y)$, or undirected, an unordered pair $\{x, y\}$; there are no loops and at most one arc leading from a node to another. $G$ is **unicursal** if there is a closed route $x_0, a_0, x_1, \dots, a_{m-1}, x_m = x_0$ (each directed arc traversed with its direction, undirected arcs either way, nodes may repeat; a single node counts as a closed route) containing each arc of $G$ exactly once and each node of $G$ at least once.
--
--   Then $G$ is unicursal if and only if
--
--   1. $G$ is **connected** (there is at least one node, and any two nodes are joined by a path, arcs traversed in either direction);
--   2. every node of $G$ is incident with an even number of arcs (directed and undirected counted together);
--   3. for every $X \subseteq N$, with $\bar X = N - X$,
--   $$d^+(X) - d^-(X) \le u(X),$$
--   where $d^+(X)$ is the number of directed arcs from $X$ to $\bar X$, $d^-(X)$ the number of directed arcs from $\bar X$ to $X$, and $u(X)$ the number of undirected arcs joining $X$ and $\bar X$.
--
--   For directed graphs condition 3 says that every node has as many incoming as outgoing arcs, and for undirected graphs it is vacuous, so the theorem contains Euler's criteria for both. The book proves sufficiency through the circulation theorem.
--
--   **Formalization Note** Unicursality is defined by the existence of a closed route (`FlowsNetworks.Graphs.MixedGraph.Unicursal`), not by conditions 1–3. Condition 3 is quantified over every subset $X$ of $N$, not only single nodes, and its difference is taken in $\mathbb Z$. Connectedness requires a nonempty node set, so the graph with no nodes is neither unicursal nor connected. An undirected arc and a directed arc never join the same pair of nodes (the book's "at most one arc"), while directed arcs $(x, y)$ and $(y, x)$ may both be present.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, pp. 42–43, Theorem 7.1

import Mathlib
import Definitions.Def_FlowsNetworks_Graphs_MixedGraph

namespace FlowsNetworks.Graphs

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 7.1 (pp. 42–43). The mixed graph
`G = [N; 𝒜]` is unicursal if and only if (a) `G` is connected; (b) every node of `G` is incident
with an even number of arcs; (c) for every `X ⊆ N`, the number of directed arcs from `X` to `X̄`
minus the number of directed arcs from `X̄` to `X` is at most the number of undirected arcs
joining `X` and `X̄`. -/
theorem unicursal_iff {N : Type} [Fintype N] [DecidableEq N] (G : MixedGraph N) :
    G.Unicursal ↔
      G.Connected ∧ (∀ v : N, Even (G.degree v)) ∧
        ∀ X : Finset N, (G.dirOut X : ℤ) - (G.dirIn X : ℤ) ≤ (G.undirJoining X : ℤ) := by sorry

end FlowsNetworks.Graphs
