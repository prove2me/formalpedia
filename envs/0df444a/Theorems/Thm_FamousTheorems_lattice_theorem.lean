-- Prove2me | Theorems.Thm_FamousTheorems_lattice_theorem
-- name    : FamousTheorems.lattice_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:00.767523+00:00
-- url     : https://prove2.me/theorems/c2b5d0e8-d049-40ec-9440-b59422dbfc68
-- title:
--   The lattice (correspondence) theorem for groups
-- statement:
--   **The lattice theorem (correspondence theorem).** Let $N$ be a normal subgroup of a group $G$. Taking preimages under the quotient map $G\to G/N$ is an order isomorphism
--   $$\{\text{subgroups of }G/N\}\;\cong\;\{\text{subgroups }H\text{ of }G\text{ with }N\le H\}.$$
--
--   It is also called the fourth isomorphism theorem. Every question about subgroups of a quotient becomes a question about subgroups of $G$ containing $N$, and the bijection preserves inclusions, joins and meets (and normality and indices).
--
--   **Formalization note.** Mathlib's `QuotientGroup.comapMk'OrderIso N`. The statement asserts an order isomorphism whose forward map is `Subgroup.comap (QuotientGroup.mk' N)`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `QuotientGroup.comapMk'OrderIso`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem lattice_theorem {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    ∃ e : Subgroup (G ⧸ N) ≃o {H : Subgroup G // N ≤ H},
      ∀ K : Subgroup (G ⧸ N), (e K : Subgroup G) = Subgroup.comap (QuotientGroup.mk' N) K := by sorry

end FamousTheorems
