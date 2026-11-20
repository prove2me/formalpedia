-- Prove2me | Theorems.Thm_DeletionCode_BlockPartition_blocks_support_disjoint
-- name    : DeletionCode.BlockPartition.blocks_support_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:18.930096+00:00
-- url     : https://prove2.me/theorems/61168ee8-b204-46de-b5c9-57729da46363
-- title:
--   Block Partition: blocks support disjoint
-- statement:
--   Sharing even one actual support vertex would merge two old rule blocks.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L71-L85
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L71-L85

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks

theorem DeletionCode.BlockPartition.blocks_support_disjoint {k : ℕ} (U : RuleSet k) :
    ∀ B ∈ blocks U, ∀ C ∈ blocks U, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v := by sorry
