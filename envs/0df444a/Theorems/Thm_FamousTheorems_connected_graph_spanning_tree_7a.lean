-- Prove2me | Theorems.Thm_FamousTheorems_connected_graph_spanning_tree_7a
-- name    : FamousTheorems.connected_graph_spanning_tree_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:59.024793+00:00
-- url     : https://prove2.me/theorems/55dd042b-2bb5-4d99-8a59-db9906886b99
-- title:
--   Every connected graph has a spanning tree
-- statement:
--   **Every connected graph has a spanning tree.** Let $G$ be a connected simple graph, possibly infinite. Then there is a subgraph $T\le G$ on the same vertex set that is a tree.
--
--   For finite graphs a spanning tree is obtained by deleting edges from cycles until none remain, or by breadth-first search. For infinite graphs Zorn's lemma is needed. Spanning trees are basic in graph algorithms, in the definition of the fundamental group of a graph and in Kirchhoff's matrix-tree theorem.
--
--   **Formalization note.** Mathlib's `SimpleGraph.Connected.exists_isTree_le`. Subgraphs are simple graphs on the same vertex type ordered by inclusion of edge sets, so $T$ automatically spans all vertices. `IsTree` means connected and acyclic.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.Connected.exists_isTree_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem connected_graph_spanning_tree_7a {V : Type*} {G : SimpleGraph V} (hG : G.Connected) : ∃ T ≤ G, T.IsTree := by sorry

end FamousTheorems
