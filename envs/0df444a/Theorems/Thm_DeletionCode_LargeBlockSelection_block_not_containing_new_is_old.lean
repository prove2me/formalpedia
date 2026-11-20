-- Prove2me | Theorems.Thm_DeletionCode_LargeBlockSelection_block_not_containing_new_is_old
-- name    : DeletionCode.LargeBlockSelection.block_not_containing_new_is_old
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:33.585902+00:00
-- url     : https://prove2.me/theorems/234bcc8d-b27b-44af-8014-9a89bdc7e04d
-- title:
--   Large Block Selection: block not containing new is old
-- statement:
--   Any actual new block excluding w is an actual old block.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L48-L58
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L48-L58

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
set_option autoImplicit true
open DeletionCode DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction

theorem DeletionCode.LargeBlockSelection.block_not_containing_new_is_old {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (B : RuleSet k)
    (hB : B ∈ blocks (insert w G)) (hw : w ∉ B) : B ∈ blocks G := by sorry
