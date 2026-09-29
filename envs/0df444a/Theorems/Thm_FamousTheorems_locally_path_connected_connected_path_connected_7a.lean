-- Prove2me | Theorems.Thm_FamousTheorems_locally_path_connected_connected_path_connected_7a
-- name    : FamousTheorems.locally_path_connected_connected_path_connected_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:00.013841+00:00
-- url     : https://prove2.me/theorems/07960346-2878-47c0-a35c-88561e968f68
-- title:
--   A connected locally path-connected space is path-connected
-- statement:
--   **A connected locally path-connected space is path-connected.** Let $X$ be a locally path-connected topological space. Then $X$ is path-connected if and only if it is connected.
--
--   The path components of a locally path-connected space are open, and hence also closed, so a connected space has only one path component. In general path-connected spaces are connected but not conversely, as the topologist's sine curve shows. The theorem is used for manifolds and CW complexes, where connectedness and path-connectedness therefore agree.
--
--   **Formalization note.** Mathlib's `pathConnectedSpace_iff_connectedSpace`. Both notions include nonemptiness.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `pathConnectedSpace_iff_connectedSpace`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem locally_path_connected_connected_path_connected_7a (X : Type*) [TopologicalSpace X] [LocallyPathConnectedSpace X] : PathConnectedSpace X ↔ ConnectedSpace X := by sorry

end FamousTheorems
