-- Prove2me | Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
-- name    : DeletionCode.BlockPartition.mem_attachedBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:01.570756+00:00
-- url     : https://prove2.me/theorems/1c8f08f0-bbd4-47bb-9823-a7d6b0733c52
-- title:
--   Block Partition: mem attached Blocks
-- statement:
--   The Block Partition construction uses the mem attached Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L93-L98
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L93-L98

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks

theorem DeletionCode.BlockPartition.mem_attachedBlocks {k : ℕ} (U B : RuleSet k)
    (w : Gram (windowLength k) → ℤ) :
    B ∈ attachedBlocks U w ↔
      B ∈ blocks U ∧ ∃ v, Incident B v ∧ Incident {w} v := by sorry
