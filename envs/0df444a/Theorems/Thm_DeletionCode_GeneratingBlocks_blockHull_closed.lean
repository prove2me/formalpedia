-- Prove2me | Theorems.Thm_DeletionCode_GeneratingBlocks_blockHull_closed
-- name    : DeletionCode.GeneratingBlocks.blockHull_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:08:29.77911+00:00
-- url     : https://prove2.me/theorems/4e2d15e6-afec-4cf6-ae4a-86de6862560a
-- title:
--   Generating Blocks: block Hull closed
-- statement:
--   The Generating Blocks construction uses the block Hull closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L69-L72
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L69-L72

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph

theorem DeletionCode.GeneratingBlocks.blockHull_closed {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (T : Set I) :
    BlockClosed G (blockHull G T) := by sorry
