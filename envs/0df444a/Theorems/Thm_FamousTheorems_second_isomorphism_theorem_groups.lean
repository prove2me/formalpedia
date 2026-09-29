-- Prove2me | Theorems.Thm_FamousTheorems_second_isomorphism_theorem_groups
-- name    : FamousTheorems.second_isomorphism_theorem_groups
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:36.272401+00:00
-- url     : https://prove2.me/theorems/308deedb-615d-46e9-bc0e-31826c9ecfb9
-- title:
--   The second isomorphism theorem for groups
-- statement:
--   **The second isomorphism theorem for groups.** Let $G$ be a group, $H\le G$ a subgroup and $N\trianglelefteq G$ a normal subgroup. Then
--   $$H/(H\cap N)\;\cong\;HN/N.$$
--
--   This is also called the diamond isomorphism theorem. With the first and third isomorphism theorems it forms the basic toolkit of group theory, and it is used in the Jordan–Hölder and Schreier refinement theorems.
--
--   **Formalization note.** Mathlib's `QuotientGroup.quotientInfEquivProdNormalQuotient`, which constructs the isomorphism; the statement asserts that a group isomorphism exists. $H\cap N$ is expressed as `N.subgroupOf H`, the subgroup $N$ viewed inside $H$, and $HN$ is the subgroup join `H ⊔ N`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `QuotientGroup.quotientInfEquivProdNormalQuotient`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem second_isomorphism_theorem_groups {G : Type*} [Group G] (H N : Subgroup G) [N.Normal] :
    Nonempty (H ⧸ N.subgroupOf H ≃* ↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) := by sorry

end FamousTheorems
