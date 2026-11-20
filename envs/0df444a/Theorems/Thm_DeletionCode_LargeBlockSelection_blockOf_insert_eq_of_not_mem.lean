-- Prove2me | Theorems.Thm_DeletionCode_LargeBlockSelection_blockOf_insert_eq_of_not_mem
-- name    : DeletionCode.LargeBlockSelection.blockOf_insert_eq_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:42.37843+00:00
-- url     : https://prove2.me/theorems/3d684a19-be62-45eb-b477-16288ade2400
-- title:
--   Large Block Selection: block Of insert eq of not mem
-- statement:
--   A block that does not contain the new rule is unchanged. No freshness
--   assumption on w, or membership assumption on its representative a, is needed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L27-L45
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L27-L45

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
set_option autoImplicit true
open DeletionCode DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction

theorem DeletionCode.LargeBlockSelection.blockOf_insert_eq_of_not_mem {k : ℕ} (G : RuleSet k)
    (w a : Gram (windowLength k) → ℤ)
    (hw : w ∉ blockOf (insert w G) a) :
    blockOf (insert w G) a = blockOf G a := by sorry
