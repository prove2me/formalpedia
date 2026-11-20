-- Prove2me | Theorems.Thm_DeletionCode_FiniteRelationBlocks_selected_block_meets
-- name    : DeletionCode.FiniteRelationBlocks.selected_block_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:47.16186+00:00
-- url     : https://prove2.me/theorems/f74c02b8-cc9a-46e4-b7f4-e04e0e9cdaaf
-- title:
--   Finite Relation Blocks: selected block meets
-- statement:
--   Each selected block shares an actual incident de Bruijn vertex with w.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L108-L120
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L108-L120

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators

theorem DeletionCode.FiniteRelationBlocks.selected_block_meets {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hind : LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ)))
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ))
    (B : RuleSet k) (hB : B ∈ selectedBlocks G I) :
    ∃ v, Incident B v ∧ Incident {w} v := by sorry
