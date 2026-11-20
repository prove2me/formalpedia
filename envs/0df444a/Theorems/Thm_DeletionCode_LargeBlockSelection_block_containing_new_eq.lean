-- Prove2me | Theorems.Thm_DeletionCode_LargeBlockSelection_block_containing_new_eq
-- name    : DeletionCode.LargeBlockSelection.block_containing_new_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:36.660185+00:00
-- url     : https://prove2.me/theorems/3d42825a-7010-41b8-89a8-f52ccfff9687
-- title:
--   Large Block Selection: block containing new eq
-- statement:
--   An actual block containing w is the actual block represented by w.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L61-L69
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L61-L69

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
set_option autoImplicit true
open DeletionCode DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction

theorem DeletionCode.LargeBlockSelection.block_containing_new_eq {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (B : RuleSet k)
    (hB : B ∈ blocks (insert w G)) (hw : w ∈ B) :
    B = blockOf (insert w G) w := by sorry
