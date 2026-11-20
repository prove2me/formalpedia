-- Prove2me | Theorems.Thm_DeletionCode_BlockPartition_blockOf_nonempty
-- name    : DeletionCode.BlockPartition.blockOf_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:16.254683+00:00
-- url     : https://prove2.me/theorems/9907365a-1655-4fd8-9fc2-575c5b41101c
-- title:
--   Block Partition: block Of nonempty
-- statement:
--   The Block Partition construction uses the block Of nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L41-L44
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L41-L44

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks

theorem DeletionCode.BlockPartition.blockOf_nonempty {k : ℕ} (U : RuleSet k)
    (a : Gram (windowLength k) → ℤ) (ha : a ∈ U) : (blockOf U a).Nonempty := by sorry
