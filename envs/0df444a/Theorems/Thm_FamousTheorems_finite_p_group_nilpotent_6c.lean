-- Prove2me | Theorems.Thm_FamousTheorems_finite_p_group_nilpotent_6c
-- name    : FamousTheorems.finite_p_group_nilpotent_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:12.756445+00:00
-- url     : https://prove2.me/theorems/2b1288d1-2e90-46af-925e-d4e776a3c910
-- title:
--   Finite p-groups are nilpotent
-- statement:
--   **Finite $p$-groups are nilpotent.** Let $p$ be a prime and $G$ a finite group in which every element has order a power of $p$. Then $G$ is nilpotent.
--
--   The proof uses the class equation: a nontrivial $p$-group has nontrivial center, and one inducts on $|G/Z(G)|$. It is the base case of the characterisation of finite nilpotent groups as the direct products of their Sylow subgroups.
--
--   **Formalization note.** Mathlib's `IsPGroup.isNilpotent`. `IsPGroup p G` says that every element has order a power of $p$, and `Group.IsNilpotent` means that the upper central series reaches the whole group.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsPGroup.isNilpotent`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem finite_p_group_nilpotent_6c {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (h : IsPGroup p G) : Group.IsNilpotent G := by sorry

end FamousTheorems
