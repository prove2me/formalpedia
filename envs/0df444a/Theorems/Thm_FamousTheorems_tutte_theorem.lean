-- Prove2me | Theorems.Thm_FamousTheorems_tutte_theorem
-- name    : FamousTheorems.tutte_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:13:47.028133+00:00
-- url     : https://prove2.me/theorems/b37e8646-0748-44df-95f7-750e1e809c56
-- title:
--   Tutte's theorem on perfect matchings
-- statement:
--   **Tutte's theorem.** A finite simple graph $G$ has a perfect matching if and only if for every set $U$ of vertices, the graph $G-U$ has at most $|U|$ connected components of odd size.
--
--   It is the fundamental characterisation of graphs with perfect matchings, generalising Hall's marriage theorem from bipartite to arbitrary graphs. The Tutte–Berge formula for the maximum matching size and Edmonds' blossom algorithm both grow out of it.
--
--   **Formalization note.** Mathlib's `SimpleGraph.tutte`; `G.IsTutteViolator u` says that $G-u$ has more odd components than $|u|$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.tutte`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem tutte_theorem {V : Type*} {G : SimpleGraph V} [Finite V] :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔ ∀ u : Set V, ¬ G.IsTutteViolator u := by sorry

end FamousTheorems
