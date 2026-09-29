-- Prove2me | Theorems.Thm_FamousTheorems_alternating_group_simple
-- name    : FamousTheorems.alternating_group_simple
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:08.443781+00:00
-- url     : https://prove2.me/theorems/4df855e4-f478-48d2-b021-5fcd771ef7b1
-- title:
--   Simplicity of the alternating group A_n for n ≥ 5
-- statement:
--   **Simplicity of the alternating group $A_n$ for $n\ge5$.** Let $\alpha$ be a finite set with at least $5$ elements. Then the alternating group $A(\alpha)$ of even permutations of $\alpha$ is a simple group.
--
--   Galois discovered this for $n\ge5$, and it is the group-theoretic reason for the insolubility of the general quintic (Abel–Ruffini). The groups $A_n$, $n\ge5$, form one of the infinite families in the classification of finite simple groups. $A_4$ is not simple: it has the Klein four-group as a normal subgroup.
--
--   **Formalization note.** Mathlib's `alternatingGroup.isSimpleGroup`. `alternatingGroup α` is the kernel of the sign homomorphism on `Equiv.Perm α`, and `IsSimpleGroup` means nontrivial with no normal subgroups other than `⊥` and `⊤`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `alternatingGroup.isSimpleGroup`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem alternating_group_simple {α : Type*} [DecidableEq α] [Fintype α] (h : 5 ≤ Nat.card α) : IsSimpleGroup (alternatingGroup α) := by sorry

end FamousTheorems
