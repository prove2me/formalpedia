-- Prove2me | Theorems.Thm_DeletionCode_FiniteRelationBlocks_selectedBlocks_subset_attachedBlocks
-- name    : DeletionCode.FiniteRelationBlocks.selectedBlocks_subset_attachedBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:27.639127+00:00
-- url     : https://prove2.me/theorems/a7a1e95d-510e-4420-a242-6612b1f1adec
-- title:
--   Finite Relation Blocks: selected Blocks subset attached Blocks
-- statement:
--   Selection by a nonzero relation coefficient implies actual attachment.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L123-L133
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L123-L133

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators

theorem DeletionCode.FiniteRelationBlocks.selectedBlocks_subset_attachedBlocks {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hind : LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ)))
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    selectedBlocks G I ⊆ attachedBlocks G w := by sorry
