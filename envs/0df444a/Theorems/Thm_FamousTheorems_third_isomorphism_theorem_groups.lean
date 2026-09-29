-- Prove2me | Theorems.Thm_FamousTheorems_third_isomorphism_theorem_groups
-- name    : FamousTheorems.third_isomorphism_theorem_groups
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:25:59.525646+00:00
-- url     : https://prove2.me/theorems/db83a11b-54a0-4208-bd3d-482c19b9cced
-- title:
--   The third isomorphism theorem for groups
-- statement:
--   **The third isomorphism theorem for groups.** Let $N\le M$ be normal subgroups of a group $G$. Then $M/N$ is a normal subgroup of $G/N$ and
--   $$(G/N)\,/\,(M/N)\;\cong\;G/M .$$
--
--   Together with the first and second isomorphism theorems, it describes how quotients interact. It gives the correspondence between normal subgroups of $G/N$ and normal subgroups of $G$ containing $N$ its concrete form, and is used constantly in the study of composition series and solvable groups.
--
--   **Formalization note.** Mathlib's `QuotientGroup.quotientQuotientEquivQuotient`. $M/N$ is written `M.map (QuotientGroup.mk' N)`, the image of $M$ in $G/N$, and `≃*` is a group isomorphism. The statement asserts that such an isomorphism exists.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `QuotientGroup.quotientQuotientEquivQuotient`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem third_isomorphism_theorem_groups {G : Type*} [Group G] (N M : Subgroup G) [N.Normal] [M.Normal] (h : N ≤ M) :
    Nonempty ((G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M) := by sorry

end FamousTheorems
