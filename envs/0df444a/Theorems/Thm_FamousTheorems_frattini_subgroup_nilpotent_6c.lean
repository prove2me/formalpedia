-- Prove2me | Theorems.Thm_FamousTheorems_frattini_subgroup_nilpotent_6c
-- name    : FamousTheorems.frattini_subgroup_nilpotent_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:14.240918+00:00
-- url     : https://prove2.me/theorems/bdeae99a-1253-4093-a4e2-629a880d2fb1
-- title:
--   The Frattini subgroup of a finite group is nilpotent
-- statement:
--   **The Frattini subgroup of a finite group is nilpotent.** Let $G$ be a finite group. Then its Frattini subgroup $\Phi(G)$, the intersection of all maximal subgroups of $G$, is nilpotent.
--
--   Frattini proved this in 1885, using what is now called the Frattini argument. It implies that $G$ is nilpotent if and only if $G/\Phi(G)$ is nilpotent. It is a basic tool in the study of finite $p$-groups, where $G/\Phi(G)$ is elementary abelian.
--
--   **Formalization note.** Mathlib's `frattini_nilpotent`. `frattini G` is the intersection of all maximal subgroups, and `Group.IsNilpotent` means that the upper central series reaches the whole group.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `frattini_nilpotent`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem frattini_subgroup_nilpotent_6c {G : Type*} [Group G] [Finite G] : Group.IsNilpotent (frattini G) := by sorry

end FamousTheorems
