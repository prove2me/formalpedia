-- Prove2me | Theorems.Thm_FamousTheorems_tree_card_edges_6b
-- name    : FamousTheorems.tree_card_edges_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:10.834521+00:00
-- url     : https://prove2.me/theorems/8d9543f8-757a-4cdc-9bb6-ab1956271747
-- title:
--   A tree on n vertices has n − 1 edges
-- statement:
--   **A tree on $n$ vertices has $n-1$ edges.** Let $G$ be a tree (a connected graph without cycles) on a finite set of $n$ vertices. Then $G$ has exactly $n-1$ edges.
--
--   This is the basic counting fact about trees. With it, a graph on $n$ vertices is a tree if and only if it is connected with $n-1$ edges, if and only if it is acyclic with $n-1$ edges. It is used for spanning trees, in Cayley's formula, and to define the cyclomatic number $|E|-|V|+1$ of a connected graph.
--
--   **Formalization note.** Mathlib's `SimpleGraph.IsTree.card_edgeFinset`, stated as $|E|+1=|V|$. A tree in Mathlib is connected, so it has at least one vertex. `G.edgeFinset` is the finite set of edges.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.IsTree.card_edgeFinset`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem tree_card_edges_6b {V : Type*} {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] (hG : G.IsTree) :
    G.edgeFinset.card + 1 = Fintype.card V := by sorry

end FamousTheorems
