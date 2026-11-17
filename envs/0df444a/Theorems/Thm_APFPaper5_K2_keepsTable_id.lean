-- Prove2me | Theorems.Thm_APFPaper5_K2_keepsTable_id
-- name    : APFPaper5.K2.keepsTable_id
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:40:20.992721+00:00
-- url     : https://prove2.me/theorems/067b3895-3c7f-447d-bb9f-f3407637e244
-- title:
--   keepsTable id
-- statement:
--   Result: keepsTable id. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem keepsTable_id (G : ι → ι → ℝ) : KeepsTable G id
--   ```
--
--   Module context and limits: KeepsTable remains explicit, as do symmetry, faithful diagonal and SourceCounted where used. The author-adopted reading is not a derivation from installed inputs. Inverse permutations and null-combination closure do not establish admitted inverse words or full K2 closure.
--
--   Source scope parameters:
--
--   ```lean
--   universe uI uK
--   variable {ι : Type uI}
--   variable [Fintype ι]
--   variable {D P R Record : Type*} {ι' : Type*} [Fintype ι'] [DecidableEq ι'] [DecidableEq D]
--     [Fintype Record]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_holds_keep_table:59; pullbacks v39; source SHA-256 504b1bcaf41d4218cb5bab47f8fe935a16187393f6044caef3b236d53fed36dd']

import Definitions.Def_APFPaper5_K2_holds_keep_table_Vocabulary
import Definitions.Def_APFPaper5_K2_HoldScore
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_id
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_comp
import Theorems.Thm_APFPaper5_K2_nothingDrawn_of_rearranges
import Theorems.Thm_APFPaper5_K2_exists_rearranges_of_nothingDrawn
import Theorems.Thm_APFPaper5_K2_heldAfter_id
import Theorems.Thm_APFPaper5_K2_heldAfter_comp
import Theorems.Thm_APFPaper5_K2_heldAfter_add
import Theorems.Thm_APFPaper5_K2_heldAfter_smul
import Theorems.Thm_APFPaper5_K2_heldAfter_markClass
import Theorems.Thm_APFPaper5_K2_holdScore_id
import Theorems.Thm_APFPaper5_K2_holdScore_marks
import Theorems.Thm_APFPaper5_K2_holdScore_isBilinear
import Theorems.Thm_APFPaper5_K2_holdScore_eq_sum
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_of_keeps
import Theorems.Thm_APFPaper5_K2_keeps_of_reverse_is_inverse
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_iff_keeps
import Theorems.Thm_APFPaper5_K2_tableForm_heldAfter_of_keeps
import Theorems.Thm_APFPaper5_K2_ends_reversed_of_keeps
import Theorems.Thm_APFPaper5_K2_keepsTable_diag
import Theorems.Thm_APFPaper5_K2_not_keepsTable_of_diag_ne
import Theorems.Thm_APFPaper5_K2_holdScoreNull_iff_tables
import Theorems.Thm_APFPaper5_K2_source_hold_score_marks
import Theorems.Thm_APFPaper5_K2_source_hold_ends_reversed
set_option autoImplicit false
universe apfNative_uI

theorem APFPaper5.K2.keepsTable_id :
∀ {ι : Type apfNative_uI} (G : ι → ι → Real), @APFPaper5.K2.KeepsTable.{apfNative_uI} ι G (@id.{apfNative_uI + 1} ι) := by sorry
