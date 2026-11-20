-- Prove2me | Theorems.Thm_DeletionCode_FiniteRelationBlocks_selectedBlocks_biUnion
-- name    : DeletionCode.FiniteRelationBlocks.selectedBlocks_biUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:39.529535+00:00
-- url     : https://prove2.me/theorems/39e776c8-38b3-4271-9c66-975ac362070f
-- title:
--   Finite Relation Blocks: selected Blocks bi Union
-- statement:
--   The finite union of precisely the selected blocks is the existing actual
--   block hull of I in G. This is a partition identity, independent of the relation.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L158-L183
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L158-L183

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators

theorem DeletionCode.FiniteRelationBlocks.selectedBlocks_biUnion {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G) :
    (selectedBlocks G I).biUnion id = RelationBlockSavings.blockHull G I := by sorry
