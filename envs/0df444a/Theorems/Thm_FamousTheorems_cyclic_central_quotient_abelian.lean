-- Prove2me | Theorems.Thm_FamousTheorems_cyclic_central_quotient_abelian
-- name    : FamousTheorems.cyclic_central_quotient_abelian
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:15.152999+00:00
-- url     : https://prove2.me/theorems/6b569ed4-e127-40e4-a53c-12f68e8d9a48
-- title:
--   A group whose central quotient is cyclic is abelian
-- statement:
--   **A group whose central quotient is cyclic is abelian.** Let $G$ be a group with centre $Z(G)$. If $G/Z(G)$ is cyclic, then $G$ is abelian.
--
--   This standard lemma of elementary group theory is used constantly in classifying small groups. For example, it shows that $G/Z(G)$ is never cyclic of prime order, and that groups of order $p^2$ are abelian. For non-abelian $G$ it gives $[G:Z(G)]\ne p$.
--
--   **Formalization note.** Mathlib's `isMulCommutative_of_isCyclic_quotient_center_self`. The cyclicity of `G ⧸ Subgroup.center G` is an instance hypothesis, and `IsMulCommutative G` says that multiplication in `G` is commutative.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isMulCommutative_of_isCyclic_quotient_center_self`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cyclic_central_quotient_abelian (G : Type*) [Group G] [IsCyclic (G ⧸ Subgroup.center G)] : IsMulCommutative G := by sorry

end FamousTheorems
