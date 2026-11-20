-- Prove2me | Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
-- name    : DeletionCode.BlockPartition.mem_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:12.743547+00:00
-- url     : https://prove2.me/theorems/09a36c42-95a2-4486-9172-26cbdbebdff0
-- title:
--   Block Partition: mem blocks
-- statement:
--   The Block Partition construction uses the mem blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L36-L39
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L36-L39

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks

theorem DeletionCode.BlockPartition.mem_blocks {k : ℕ} (U B : RuleSet k) :
    B ∈ blocks U ↔ ∃ a ∈ U, blockOf U a = B := by sorry
