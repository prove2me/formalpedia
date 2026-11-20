-- Prove2me | Theorems.Thm_DeletionCode_GeneratingBlocks_subset_blockHull
-- name    : DeletionCode.GeneratingBlocks.subset_blockHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:09:32.175175+00:00
-- url     : https://prove2.me/theorems/3dbb5d9b-df18-44a2-8dec-e42643eb8ff4
-- title:
--   Generating Blocks: subset block Hull
-- statement:
--   The Generating Blocks construction uses the subset block Hull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L64-L67
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L64-L67

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph

theorem DeletionCode.GeneratingBlocks.subset_blockHull {I : Type*} {L : ℕ} (G : I → Gram L → ℤ) (T : Set I) :
    T ⊆ blockHull G T := by sorry
