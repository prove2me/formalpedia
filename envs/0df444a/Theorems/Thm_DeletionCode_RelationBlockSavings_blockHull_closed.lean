-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_closed
-- name    : DeletionCode.RelationBlockSavings.blockHull_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:38.982644+00:00
-- url     : https://prove2.me/theorems/c5600d59-886b-48f0-9271-b7f5e7670e43
-- title:
--   Relation Block Savings: block Hull closed
-- statement:
--   The Relation Block Savings construction uses the block Hull closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L146-L153
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L146-L153

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
import Theorems.Thm_DeletionCode_GeneratingBlocks_blockHull_closed

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSavings.blockHull_closed {k : ℕ} (G I : RuleSet k)
    {a b : Gram (windowLength k) → ℤ} (ha : a ∈ blockHull G I)
    (hpath : Relation.EqvGen (FiniteConnectedGrowth.Induced G RuleAdjacent) a b) :
    b ∈ blockHull G I := by sorry
