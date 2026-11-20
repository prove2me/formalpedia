-- Prove2me | Theorems.Thm_DeletionCode_BlockAdjunction_path_within_block
-- name    : DeletionCode.BlockAdjunction.path_within_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:05.034598+00:00
-- url     : https://prove2.me/theorems/2a95db81-9984-4a99-b88d-ebd9efd656f4
-- title:
--   Block Adjunction: path within block
-- statement:
--   Paths within an equivalence class can be restricted to that class itself.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L25-L46
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L25-L46

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition

theorem DeletionCode.BlockAdjunction.path_within_block {k : ℕ} (U : RuleSet k)
    {b c : Gram (windowLength k) → ℤ} (hbc : ConnectedIn U b c) :
    ∀ a, ConnectedIn U a b → ConnectedIn (blockOf U a) b c := by sorry
