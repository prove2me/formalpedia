-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_subset
-- name    : DeletionCode.RelationBlockSavings.blockHull_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:49.537967+00:00
-- url     : https://prove2.me/theorems/cf3256a4-13e2-4c91-84a2-c43eca07fa5b
-- title:
--   Relation Block Savings: block Hull subset
-- statement:
--   The Relation Block Savings construction uses the block Hull subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L127-L129
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L127-L129

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSavings.blockHull_subset {k : ℕ} (G I : RuleSet k) : blockHull G I ⊆ G := by sorry
