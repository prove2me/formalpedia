-- Prove2me | Theorems.Thm_DeletionCode_BlockPartition_blockOf_eq_of_connected
-- name    : DeletionCode.BlockPartition.blockOf_eq_of_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:12.614443+00:00
-- url     : https://prove2.me/theorems/98c381de-9084-4d51-b494-b8927d11aea4
-- title:
--   Block Partition: block Of eq of connected
-- statement:
--   The Block Partition construction uses the block Of eq of connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L46-L56
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L46-L56

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks

theorem DeletionCode.BlockPartition.blockOf_eq_of_connected {k : ℕ} (U : RuleSet k)
    (a b : Gram (windowLength k) → ℤ) (hab : ConnectedIn U a b) :
    blockOf U a = blockOf U b := by sorry
