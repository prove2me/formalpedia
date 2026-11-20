-- Prove2me | Theorems.Thm_DeletionCode_FiniteRelationBlocks_relation_support_included
-- name    : DeletionCode.FiniteRelationBlocks.relation_support_included
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:32.324006+00:00
-- url     : https://prove2.me/theorems/063c22c8-6a60-4f5c-acca-b15a5240bc0d
-- title:
--   Finite Relation Blocks: relation support included
-- statement:
--   A linear combination cannot introduce a gram outside the actual support
--   union of the ambient rules. Independence and nonzero coefficients are unneeded.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L137-L154
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean#L137-L154

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators

theorem DeletionCode.FiniteRelationBlocks.relation_support_included {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    SupportInclusion.CoordinateSupportIncluded {w} G := by sorry
