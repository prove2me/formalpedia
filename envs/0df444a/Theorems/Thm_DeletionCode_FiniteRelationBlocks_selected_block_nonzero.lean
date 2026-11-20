-- Prove2me | Theorems.Thm_DeletionCode_FiniteRelationBlocks_selected_block_nonzero
-- name    : DeletionCode.FiniteRelationBlocks.selected_block_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:54.692716+00:00
-- url     : https://prove2.me/theorems/98b84930-2be8-4c86-be57-4e6261c4a61f
-- title:
--   Finite Relation Blocks: selected block nonzero
-- statement:
--   Every selected actual adjacency block has a gram of one of its rules that
--   survives in the relation vector. No nonzero-restriction premise is required.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L73-L105
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L73-L105

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators

theorem DeletionCode.FiniteRelationBlocks.selected_block_nonzero {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hind : LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ)))
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ))
    (B : RuleSet k) (hB : B ∈ selectedBlocks G I) :
    ∃ g u, u ∈ B ∧ u g ≠ 0 ∧ w g ≠ 0 := by sorry
