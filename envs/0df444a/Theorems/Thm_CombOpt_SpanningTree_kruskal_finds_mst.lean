-- Prove2me | Theorems.Thm_CombOpt_SpanningTree_kruskal_finds_mst
-- name    : CombOpt.SpanningTree.kruskal_finds_mst
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:13.770972+00:00
-- url     : https://prove2.me/theorems/4dbed109-e1a5-41b1-b4fe-661839f04a6b
-- title:
--   Theorem 2.6 — Kruskal's Algorithm finds a minimum spanning tree
-- statement:
--   Let $G$ be a connected graph with arbitrary real edge costs $c$. Run **Kruskal's Algorithm**: start from $F=\emptyset$; at each step add to $F$ a least-cost edge $e\notin F$ such that $(V,F)$ remains a forest; stop when $(V,F)$ is a spanning tree. Then, whatever choices are made among edges of equal cost, the algorithm finds a minimum spanning tree. Precisely, for every edge set $F$ reachable from $\emptyset$ by steps of the algorithm:
--
--   1. if $(V,F)$ is not a spanning tree, a further step from $F$ is possible;
--   2. if $(V,F)$ is a spanning tree, then $F$ is a minimum spanning tree.
--
--   **Formalization Note** Each step adds a new edge, so every run stops after at most $|E|$ steps; with 1 and 2, every run ends with an MST. Reachability is the reflexive–transitive closure of the one-step relation `KruskalStep`.
--
--   Differences from the source:
--   - encoding: Kruskal's Algorithm finds a minimum spanning tree → every F reachable from ∅ by KruskalStep admits a further step unless it is a spanning tree, and is an MST when it is a spanning tree; reason: each step adds a new edge, so runs are finite; the two clauses say that every run, for every tie-breaking, stops and stops at an MST
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 2.6, p. 13 (PDF p. 22); Kruskal's Algorithm, p. 11 (PDF p. 20)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsMST
import Definitions.Def_CombOpt_SpanningTree_Graph_KruskalStep

namespace CombOpt.SpanningTree

/-- **Theorem 2.6: Kruskal's Algorithm finds a minimum spanning tree.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 2.6, p. 13 (PDF p. 22): "For any connected graph G with arbitrary edge costs c,
Kruskal's Algorithm finds a minimum spanning tree." The algorithm (p. 11): "Keep a spanning forest
H = (V, F) of G, with F = ∅ initially. At each step add to F a least-cost edge e ∉ F such that H
remains a forest. Stop when H is a spanning tree."

Let `G` be connected and `c` arbitrary real costs. For every edge set `F` reachable from `∅` by
steps of the algorithm (with any tie-breaking):
1. if `(V, F)` is not a spanning tree, the algorithm can make a further step from `F` (it never
   gets stuck before it stops);
2. if `(V, F)` is a spanning tree (the algorithm stops), then `F` is a minimum spanning tree.

**Formalization Note.** Each step adds one new edge, so every run stops after at most `|E|` steps;
together with (1) and (2), every run of the algorithm, for every tie-breaking, ends with an MST.
`Relation.ReflTransGen` is the reflexive–transitive closure of the step relation. -/
theorem kruskal_finds_mst {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Graph V E)
    (hG : G.SpanConnected Finset.univ) (c : E → ℝ) (F : Finset E)
    (hF : Relation.ReflTransGen (G.KruskalStep c) ∅ F) :
    (¬ G.IsSpanningTree F → ∃ F' : Finset E, G.KruskalStep c F F') ∧
      (G.IsSpanningTree F → G.IsMST c F) := by sorry

end CombOpt.SpanningTree
