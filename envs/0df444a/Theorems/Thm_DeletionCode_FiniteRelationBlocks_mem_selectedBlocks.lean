-- Prove2me | Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
-- name    : DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:20.540178+00:00
-- url     : https://prove2.me/theorems/a65be123-6bbf-4908-9fd0-05fce3ec32b7
-- title:
--   Finite Relation Blocks: mem selected Blocks
-- statement:
--   The Finite Relation Blocks construction uses the mem selected Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L23-L26
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L23-L26

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators

theorem DeletionCode.FiniteRelationBlocks.mem_selectedBlocks {k : ℕ} (G I B : RuleSet k) :
    B ∈ selectedBlocks G I ↔ B ∈ blocks G ∧ (B ∩ I).Nonempty := by sorry
