-- Prove2me | Theorems.Thm_DeletionCode_LargeBlockSelection_blockOf_insert_subset_of_not_mem
-- name    : DeletionCode.LargeBlockSelection.blockOf_insert_subset_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:44.868265+00:00
-- url     : https://prove2.me/theorems/992dab20-13e7-4307-a2b9-7b0370230d86
-- title:
--   Large Block Selection: block Of insert subset of not mem
-- statement:
--   A new block excluding the adjoined rule consists entirely of old rules.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L15-L23
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L15-L23

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
set_option autoImplicit true
open DeletionCode DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction

theorem DeletionCode.LargeBlockSelection.blockOf_insert_subset_of_not_mem {k : ℕ} (G : RuleSet k)
    (w a : Gram (windowLength k) → ℤ)
    (hw : w ∉ blockOf (insert w G) a) : blockOf (insert w G) a ⊆ G := by sorry
