-- Prove2me | Theorems.Thm_DeletionCode_BlockPartition_attached_blocks_union_bound
-- name    : DeletionCode.BlockPartition.attached_blocks_union_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:23.411686+00:00
-- url     : https://prove2.me/theorems/cf9f4c39-7757-4178-88a5-6dc46056efa6
-- title:
--   Block Partition: attached blocks union bound
-- statement:
--   The large-block upper estimate applied to the actual old block partition.
--   The disjoint-support condition is proved above, rather than assumed here.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L112-L125
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L112-L125

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks

theorem DeletionCode.BlockPartition.attached_blocks_union_bound {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (t L : ℕ)
    (hsize : ∀ B ∈ blocks U, B.card ≤ L)
    (hvertices : Fintype.card (RuleSetVertex {w}) ≤ 4 * t * L) :
    (insert w ((attachedBlocks U w).biUnion id)).card ≤ 1 + 4 * t * L ^ 2 := by sorry
