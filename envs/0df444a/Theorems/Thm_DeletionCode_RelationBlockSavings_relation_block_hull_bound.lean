-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSavings_relation_block_hull_bound
-- name    : DeletionCode.RelationBlockSavings.relation_block_hull_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:47.278286+00:00
-- url     : https://prove2.me/theorems/80864644-1290-4f64-9ede-6dc0d201f2a3
-- title:
--   Relation Block Savings: relation block hull bound
-- statement:
--   The component estimate for the relation case of the bounded-witness proof,
--   applied to the union of whole ambient blocks that meet the relation support.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L184-L192
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L184-L192

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSavings.relation_block_hull_bound {t k : ℕ} (ht : 2 ≤ t) (G I : RuleSet k)
    (hIG : I ⊆ G) (hI : 2 ≤ I.card) (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount (blockHull G I) ≤ (2 * t - 1) * (blockHull G I).card := by sorry
