-- Prove2me | Theorems.Thm_DeletionCode_BlockAdjunction_blockOf_insert_eq
-- name    : DeletionCode.BlockAdjunction.blockOf_insert_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:09.05372+00:00
-- url     : https://prove2.me/theorems/0a837572-a581-4450-b268-15debd2fa0fb
-- title:
--   Block Adjunction: block Of insert eq
-- statement:
--   The new block is exactly the new rule and the old blocks touching it.
--   Freshness of w is unnecessary for this identity.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L89-L140
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L89-L140

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition

theorem DeletionCode.BlockAdjunction.blockOf_insert_eq {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) :
    blockOf (insert w U) w = insert w ((attachedBlocks U w).biUnion id) := by sorry
