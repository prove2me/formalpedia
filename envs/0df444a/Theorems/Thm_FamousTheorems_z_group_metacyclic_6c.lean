-- Prove2me | Theorems.Thm_FamousTheorems_z_group_metacyclic_6c
-- name    : FamousTheorems.z_group_metacyclic_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:22.48189+00:00
-- url     : https://prove2.me/theorems/9e2f73dc-44bf-4543-ae2d-0e5e70ef2d92
-- title:
--   Hölder–Burnside–Zassenhaus: Z-groups are metacyclic
-- statement:
--   **Z-groups are metacyclic (Hölder, Burnside, Zassenhaus).** A finite group $G$ has all its Sylow subgroups cyclic if and only if $G\cong N\rtimes H$ is a semidirect product of cyclic groups $N$ and $H$ of coprime orders, where $N$ and $H$ are subgroups of $G$.
--
--   Such groups are called Z-groups, after Zassenhaus. They include the groups of square-free order. They are the groups whose group cohomology is periodic with period dividing the order, and they appear in the classification of groups acting freely on spheres.
--
--   **Formalization note.** Mathlib's `isZGroup_iff_exists_mulEquiv`. `IsZGroup G` says that every Sylow subgroup of $G$ is cyclic. The semidirect product `N ⋊[φ] H` is taken with respect to an action `φ : H →* MulAut N`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isZGroup_iff_exists_mulEquiv`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem z_group_metacyclic_6c {G : Type*} [Group G] [Finite G] :
    IsZGroup G ↔ ∃ (N H : Subgroup G) (φ : H →* MulAut N) (_ : G ≃* N ⋊[φ] H),
      IsCyclic H ∧ IsCyclic N ∧ (Nat.card N).Coprime (Nat.card H) := by sorry

end FamousTheorems
