-- Prove2me | Theorems.Thm_DeletionCode_BlockPartition_attached_blocks_count_bound
-- name    : DeletionCode.BlockPartition.attached_blocks_count_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:19:57.293846+00:00
-- url     : https://prove2.me/theorems/3acab287-0b3a-446a-92ba-23cdfe56c137
-- title:
--   Block Partition: attached blocks count bound
-- statement:
--   The Block Partition construction uses the attached blocks count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L100-L108
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L100-L108

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks

theorem DeletionCode.BlockPartition.attached_blocks_count_bound {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) :
    (attachedBlocks U w).card ≤ Fintype.card (RuleSetVertex {w}) := by sorry
