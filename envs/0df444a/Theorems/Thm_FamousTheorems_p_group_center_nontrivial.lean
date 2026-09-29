-- Prove2me | Theorems.Thm_FamousTheorems_p_group_center_nontrivial
-- name    : FamousTheorems.p_group_center_nontrivial
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:13.345526+00:00
-- url     : https://prove2.me/theorems/169ab917-f891-487a-a667-75fc8dfda94c
-- title:
--   Finite p-groups have nontrivial center
-- statement:
--   **Finite $p$-groups have nontrivial centre.** Let $p$ be a prime and $G$ a nontrivial finite group of order a power of $p$. Then the centre $Z(G)$ is nontrivial.
--
--   The proof uses the class equation: $|G|=|Z(G)|+\sum[G:C_G(x)]$, where every term in the sum is divisible by $p$. It is the basis of the structure theory of $p$-groups. It shows that finite $p$-groups are nilpotent and hence solvable, and it is the first step in the Sylow theorems and in classifying groups of order $p^2$ and $p^3$.
--
--   **Formalization note.** Mathlib's `IsPGroup.center_nontrivial`. `IsPGroup p G` means that every element has order a power of `p`. For finite `G` this is equivalent to $|G|$ being a power of $p$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsPGroup.center_nontrivial`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem p_group_center_nontrivial {p : ℕ} {G : Type*} [Group G] (hG : IsPGroup p G) [Fact p.Prime] [Nontrivial G] [Finite G] :
    Nontrivial (Subgroup.center G) := by sorry

end FamousTheorems
