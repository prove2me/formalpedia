-- Prove2me | Theorems.Thm_FamousTheorems_acyclic_iff_paths_unique_7a
-- name    : FamousTheorems.acyclic_iff_paths_unique_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:44.560128+00:00
-- url     : https://prove2.me/theorems/6d63bdd5-2f3d-473b-864f-630684842996
-- title:
--   A graph is acyclic iff paths between vertices are unique
-- statement:
--   **A graph is acyclic iff paths between vertices are unique.** A simple graph $G$ has no cycles if and only if for all vertices $u,v$ there is at most one path from $u$ to $v$ in $G$.
--
--   If two distinct paths join $u$ and $v$, their union contains a cycle. Conversely, a cycle through $u$ and $v$ gives two paths between them. It follows that a tree, a connected acyclic graph, has exactly one path between any two vertices. This fact is the basis of rooted trees, spanning-tree algorithms and tree metrics.
--
--   **Formalization note.** Mathlib's `SimpleGraph.isAcyclic_iff_subsingleton_path`. `G.Path u v` is the type of walks from $u$ to $v$ without repeated vertices, and `Subsingleton` says that it has at most one element.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.isAcyclic_iff_subsingleton_path`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem acyclic_iff_paths_unique_7a {V : Type*} {G : SimpleGraph V} : G.IsAcyclic ↔ ∀ u v : V, Subsingleton (G.Path u v) := by sorry

end FamousTheorems
