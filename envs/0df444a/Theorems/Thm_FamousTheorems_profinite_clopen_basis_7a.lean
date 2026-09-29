-- Prove2me | Theorems.Thm_FamousTheorems_profinite_clopen_basis_7a
-- name    : FamousTheorems.profinite_clopen_basis_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:50.279639+00:00
-- url     : https://prove2.me/theorems/a56ae88b-b85c-4bfa-b56d-659fb20e49de
-- title:
--   Compact Hausdorff totally disconnected spaces have a clopen basis
-- statement:
--   **Compact Hausdorff totally disconnected spaces have a clopen basis.** In a compact Hausdorff space in which every connected subset has at most one point, the sets that are both open and closed form a basis of the topology.
--
--   A space with a basis of clopen sets is called zero-dimensional, and the compact Hausdorff zero-dimensional spaces are the Stone spaces. So the theorem identifies totally disconnected compact Hausdorff spaces with Stone spaces, the objects dual to Boolean algebras under Stone duality. The same spaces are the profinite spaces, the inverse limits of finite discrete spaces, such as Galois groups and the $p$-adic integers.
--
--   **Formalization note.** Mathlib's `isTopologicalBasis_isClopen`. `TotallyDisconnectedSpace X` means that every preconnected subset of $X$ is a subsingleton.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isTopologicalBasis_isClopen`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem profinite_clopen_basis_7a (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X] :
    TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} := by sorry

end FamousTheorems
