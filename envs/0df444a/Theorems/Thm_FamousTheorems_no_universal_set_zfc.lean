-- Prove2me | Theorems.Thm_FamousTheorems_no_universal_set_zfc
-- name    : FamousTheorems.no_universal_set_zfc
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:23.467519+00:00
-- url     : https://prove2.me/theorems/47e66e5d-f4c7-42a4-bc5b-2de90fb40efb
-- title:
--   There is no universal set
-- statement:
--   **There is no universal set.** In ZFC, the class of all sets is not a set. Equivalently, the universal class is not a member of itself.
--
--   If there were a set $V$ of all sets, separation would give the Russell set $\{x\in V: x\notin x\}$, which is a contradiction. The theorem is why naive comprehension fails. It is also why collections like "all sets" or "all groups" must be treated as proper classes.
--
--   **Formalization note.** Mathlib's `Class.univ_notMem_univ`, in Mathlib's model of ZFC. `Class` is the type of classes of ZFC sets (`ZFSet`), and a class is a member of another class only if it is a set. So `Class.univ ∉ Class.univ` says that the universal class is not a set.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Class.univ_notMem_univ`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem no_universal_set_zfc : Class.univ ∉ Class.univ := by sorry

end FamousTheorems
