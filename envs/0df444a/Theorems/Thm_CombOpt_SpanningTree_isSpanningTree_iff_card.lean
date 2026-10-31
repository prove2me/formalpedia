-- Prove2me | Theorems.Thm_CombOpt_SpanningTree_isSpanningTree_iff_card
-- name    : CombOpt.SpanningTree.isSpanningTree_iff_card
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:33.49116+00:00
-- url     : https://prove2.me/theorems/3b3eb9bf-2f62-44d8-a4a6-4a07f408ce55
-- title:
--   Lemma 2.2 — a spanning connected subgraph is a spanning tree iff it has $n-1$ edges (corrected: nonempty node set)
-- statement:
--   Let $G$ be a graph with $n=|V|\ge 1$ nodes and let $F\subseteq E$ be such that the spanning subgraph $(V,F)$ is connected. Then $(V,F)$ is a spanning tree if and only if
--   $$|F| = n-1.$$
--
--   This is the counting characterization of spanning trees used throughout the chapter, e.g. in showing that the characteristic vector of a spanning tree satisfies $x(E)=|V|-1$.
--
--   **Formalization Note** The count is compared in the integers. The hypothesis $n\ge 1$ is added: for the graph with no nodes and no edges, the empty subgraph is connected and has no circuit, so it is a spanning tree, yet it has $0\ne -1=n-1$ edges.
--
--   Differences from the source:
--   - correction: any graph G (n = |V| ≥ 0) → [Nonempty V] (n ≥ 1); reason: for V = E = ∅ the empty subgraph is a spanning connected subgraph and a spanning tree with 0 ≠ −1 = n − 1 edges, so the printed statement fails
--   - encoding: n − 1 → (Fintype.card V : ℤ) − 1, compared with (F.card : ℤ); reason: integer arithmetic avoids truncated natural subtraction; with n ≥ 1 it is the same number
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Lemma 2.2, p. 11 (PDF p. 20)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsSpanningTree

namespace CombOpt.SpanningTree

/-- **Lemma 2.2: a spanning connected subgraph is a spanning tree iff it has n − 1 edges.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Lemma 2.2, p. 11 (PDF p. 20): "A spanning connected subgraph of G is a spanning tree if and
only if it has exactly n − 1 edges", where n = |V| (p. 10).

For a graph with a nonempty finite node set and an edge set `F` such that the spanning subgraph
`(V, F)` is connected: `(V, F)` is a spanning tree if and only if `|F| = |V| − 1`.

**Formalization Note.** The count is compared in `ℤ`. The node set is assumed nonempty: with
`V = E = ∅` the empty subgraph is connected and has no circuit, hence is a spanning tree, but has
`0 ≠ −1 = n − 1` edges (see the differences list). -/
theorem isSpanningTree_iff_card {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]
    (G : Graph V E) (F : Finset E) (hF : G.SpanConnected F) :
    G.IsSpanningTree F ↔ (F.card : ℤ) = Fintype.card V - 1 := by sorry

end CombOpt.SpanningTree
