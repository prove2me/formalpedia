-- Prove2me | Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
-- name    : DeletionCode.BlockPartition.mem_blockOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:00.936868+00:00
-- url     : https://prove2.me/theorems/436663c5-f559-4a21-bdd0-644779a6c341
-- title:
--   Block Partition: mem block Of
-- statement:
--   The Block Partition construction uses the mem block Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L30-L34
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L30-L34

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks

theorem DeletionCode.BlockPartition.mem_blockOf {k : ℕ} (U : RuleSet k)
    (a b : Gram (windowLength k) → ℤ) :
    b ∈ blockOf U a ↔ b ∈ U ∧ ConnectedIn U a b := by sorry
