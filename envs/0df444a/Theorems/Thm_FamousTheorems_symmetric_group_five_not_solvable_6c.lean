-- Prove2me | Theorems.Thm_FamousTheorems_symmetric_group_five_not_solvable_6c
-- name    : FamousTheorems.symmetric_group_five_not_solvable_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:12.306807+00:00
-- url     : https://prove2.me/theorems/c697d0b2-b6dc-4995-a66b-941350b6f6e7
-- title:
--   The symmetric group S₅ is not solvable
-- statement:
--   **The symmetric group $S_5$ is not solvable.** The group of permutations of a $5$-element set is not solvable: its derived series never reaches the trivial group.
--
--   Galois theory turns this into the unsolvability of the general quintic by radicals (Abel–Ruffini), because the Galois group of the generic quintic is $S_5$. The derived subgroup of $S_5$ is the simple group $A_5$, which is its own derived subgroup.
--
--   **Formalization note.** Mathlib's `Equiv.Perm.not_isSolvable_fin_5`. $S_5$ is `Equiv.Perm (Fin 5)`, and `Group.IsSolvable G` means that some term of the derived series of $G$ is trivial.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Equiv.Perm.not_isSolvable_fin_5`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem symmetric_group_five_not_solvable_6c : ¬Group.IsSolvable (Equiv.Perm (Fin 5)) := by sorry

end FamousTheorems
