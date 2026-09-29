-- Prove2me | Theorems.Thm_FamousTheorems_jordan_primitive_three_cycle
-- name    : FamousTheorems.jordan_primitive_three_cycle
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:39.610975+00:00
-- url     : https://prove2.me/theorems/40316aa9-c027-4d26-a115-98d2e45204e3
-- title:
--   Jordan's theorem on primitive groups containing a 3-cycle
-- statement:
--   **Jordan's theorem on primitive groups containing a 3-cycle.** Let $\alpha$ be a finite set and $G\le\operatorname{Sym}(\alpha)$ a primitive permutation group. If $G$ contains a 3-cycle, then $G$ contains the alternating group $\operatorname{Alt}(\alpha)$.
--
--   With the transposition case, this is a classical criterion for recognising the full symmetric and alternating groups. It is used in computing Galois groups and in the study of multiply transitive groups.
--
--   **Formalization note.** Mathlib's `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`. Primitivity is `MulAction.IsPreprimitive G α`, and `IsThreeCycle` says that the permutation is a 3-cycle.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jordan_primitive_three_cycle {α : Type*} [Fintype α] [DecidableEq α] {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPreprimitive G α)
    {g : Equiv.Perm α} (hg : g.IsThreeCycle) (hgG : g ∈ G) : alternatingGroup α ≤ G := by sorry

end FamousTheorems
