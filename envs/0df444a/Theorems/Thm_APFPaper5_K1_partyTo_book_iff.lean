-- Prove2me | Theorems.Thm_APFPaper5_K1_partyTo_book_iff
-- name    : APFPaper5.K1.partyTo_book_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:06:49.850706+00:00
-- url     : https://prove2.me/theorems/1fa51031-8e0a-4c55-bd8e-985bd5683299
-- title:
--   partyTo book iff
-- statement:
--   Result: partyTo book iff. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem partyTo_book_iff (mark : D → W → Bool) (joint : W → Bool) (d : D) (a : W) :
--       PartyTo (keepsB mark joint) d a ↔ mark d a = true
--   ```
--
--   Module context and limits: Party membership agrees with the supplied two-kind book listing. The faithful-diagonal results require nonnegative weights plus own positive records, or the exact kernel condition. With no joint records the party score agrees with shared cost; existence of such a book is not derived.
--
--   Source scope parameters:
--
--   ```lean
--   universe u v
--   variable {D : Type u} [Fintype D] [DecidableEq D] {W : Type v}
--   variable [Fintype W]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_party_score:47; pullbacks v39; source SHA-256 d9d9d9b139282586a3fb8bd4e7845a4d9b0f58fc1fc3ed6159c6cd1779605206']

import Definitions.Def_APFPaper5_K1_PartyScore
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_form_eq_zero_iff
import Theorems.Thm_APFPaper5_K1_atomTable_faithful_iff
import Theorems.Thm_APFPaper5_K1_atomTable_row_eq_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_merge_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_eq_zero_of_disjoint
import Theorems.Thm_APFPaper5_K1_card_mul_le_sum_of_private
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor

set_option autoImplicit false

namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5
open APFPaper5.K1
universe u v
variable {D : Type u} [Fintype D] [DecidableEq D] {W : Type v}

theorem APFPaper5.K1.partyTo_book_iff (mark : D → W → Bool) (joint : W → Bool) (d : D) (a : W) :
    PartyTo (keepsB mark joint) d a ↔ mark d a = true := by sorry
