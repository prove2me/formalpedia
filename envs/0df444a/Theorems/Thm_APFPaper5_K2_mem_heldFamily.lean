-- Prove2me | Theorems.Thm_APFPaper5_K2_mem_heldFamily
-- name    : APFPaper5.K2.mem_heldFamily
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:00:35.01821+00:00
-- url     : https://prove2.me/theorems/075f7fc6-fa93-45f3-b15d-34d827424ff1
-- title:
--   mem heldFamily
-- statement:
--   Result: mem heldFamily. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem mem_heldFamily (reads : D → X → Bool) (S : Finset D) (x : X) (d : D) :
--       d ∈ heldFamily reads S x ↔ d ∈ S ∧ reads d x = true
--   ```
--
--   Module context and limits: A recorded class is the Boolean list of records kept by the listed distinctions that read true. Its cost identity is definitional and its three-class bound requires nonnegative weights. Excluding a supplied turnTable from such lists does not exclude physical quantum turns or address the unrecorded state.
--
--   Source scope parameters:
--
--   ```lean
--   universe uX uD uW
--   variable {X : Type uX} {D : Type uD} {W : Type uW}
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_recorded_classes:55; pullbacks v39; source SHA-256 7b838b50b1566bc7bd9006c2d2840d9424bf5e9bb2adceae18b87e8d3e911c2b']

import Definitions.Def_APFPaper5_K2_recorded_classes_Vocabulary
import Definitions.Def_APFPaper5_K2_StateClass
import Theorems.Thm_APFPaper5_K2_atomTable_eq_recordForm
import Theorems.Thm_APFPaper5_K2_tableForm_atomTable_eq_recordForm
import Theorems.Thm_APFPaper5_K2_activeClass_after_hold_of_no_turn
import Theorems.Thm_APFPaper5_K2_activeClass_after_turn
import Theorems.Thm_APFPaper5_K2_activeClass_cost
import Theorems.Thm_APFPaper5_K2_shared_record_counts_four
import Theorems.Thm_APFPaper5_K2_sideClass_after_hold
import Theorems.Thm_APFPaper5_K2_opposite_sides_cancel
import Theorems.Thm_APFPaper5_K2_keptClass_cost
import Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint
import Definitions.Def_APFPaper5_K1_record_tables_and_turns_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_triangle
import Theorems.Thm_APFPaper5_K1_atomTable_le_diag
import Theorems.Thm_APFPaper5_K1_sourcePartyScore_triangle
import Theorems.Thm_APFPaper5_K1_turnTable_symm
import Theorems.Thm_APFPaper5_K1_turnTable_breaks_triangle
import Theorems.Thm_APFPaper5_K1_no_record_ledger_has_turnTable
import Theorems.Thm_APFPaper5_K1_no_three_distinctions_have_turnTable
import Theorems.Thm_APFPaper5_K1_turnTable_half_form
import Theorems.Thm_APFPaper5_K1_turnTable_half_nonneg
import Theorems.Thm_APFPaper5_K1_turnTable_half_faithful
import Theorems.Thm_APFPaper5_K1_ownTable_eq
import Theorems.Thm_APFPaper5_K1_turnClass_negative
import Theorems.Thm_APFPaper5_K1_turnTable_on_classes

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2
end APFPaper5.K2
open APFPaper5
open APFPaper5.K2
universe uX uD uW
variable {X : Type uX} {D : Type uD} {W : Type uW}

theorem APFPaper5.K2.mem_heldFamily (reads : D → X → Bool) (S : Finset D) (x : X) (d : D) :
    d ∈ heldFamily reads S x ↔ d ∈ S ∧ reads d x = true := by sorry
