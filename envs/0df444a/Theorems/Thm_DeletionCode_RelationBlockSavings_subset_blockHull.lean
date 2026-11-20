-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSavings_subset_blockHull
-- name    : DeletionCode.RelationBlockSavings.subset_blockHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:47.04096+00:00
-- url     : https://prove2.me/theorems/4f996a6f-7be2-4243-9b6b-4e3dcf7da77d
-- title:
--   Relation Block Savings: subset block Hull
-- statement:
--   The Relation Block Savings construction uses the subset block Hull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L131-L134
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L131-L134

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
import Theorems.Thm_DeletionCode_GeneratingBlocks_subset_blockHull

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSavings.subset_blockHull {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G) : I ⊆ blockHull G I := by sorry
