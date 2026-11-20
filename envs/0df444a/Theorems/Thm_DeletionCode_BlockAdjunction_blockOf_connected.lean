-- Prove2me | Theorems.Thm_DeletionCode_BlockAdjunction_blockOf_connected
-- name    : DeletionCode.BlockAdjunction.blockOf_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:00.776883+00:00
-- url     : https://prove2.me/theorems/ca370f26-a0c8-46fd-b693-585ad337d851
-- title:
--   Block Adjunction: block Of connected
-- statement:
--   Every actual rule block is connected using only its own rules.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L49-L55
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L49-L55

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition

theorem DeletionCode.BlockAdjunction.blockOf_connected {k : ℕ} (U : RuleSet k)
    (a : Gram (windowLength k) → ℤ) : Connected (blockOf U a) := by sorry
