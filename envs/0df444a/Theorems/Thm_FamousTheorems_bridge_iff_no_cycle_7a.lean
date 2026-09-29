-- Prove2me | Theorems.Thm_FamousTheorems_bridge_iff_no_cycle_7a
-- name    : FamousTheorems.bridge_iff_no_cycle_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:49.165511+00:00
-- url     : https://prove2.me/theorems/b4989e4b-e7b5-48ce-8632-9aa9bc1352b3
-- title:
--   An edge is a bridge iff it lies on no cycle
-- statement:
--   **An edge is a bridge iff it lies on no cycle.** Let $e$ be an edge of a simple graph $G$. Then $e$ is a bridge, meaning that removing it disconnects its endpoints, if and only if no cycle of $G$ contains $e$.
--
--   This characterisation is used for the structure of graphs through their $2$-edge-connected components, for Robbins' theorem that a graph has a strongly connected orientation if and only if it is connected and bridgeless, and for linear-time bridge-finding algorithms.
--
--   **Formalization note.** Mathlib's `SimpleGraph.isBridge_iff_forall_cycle_notMem`. `G.IsBridge e` says that $e$ is an edge and its endpoints are not reachable from each other in $G$ with $e$ deleted. Cycles are closed walks `p : G.Walk u u` with `p.IsCycle`, and `p.edges` is the list of their edges.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.isBridge_iff_forall_cycle_notMem`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem bridge_iff_no_cycle_7a {V : Type*} {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ G.edgeSet) :
    G.IsBridge e ↔ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges := by sorry

end FamousTheorems
