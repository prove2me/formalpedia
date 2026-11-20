-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSavings_relation_seeded_bound
-- name    : DeletionCode.RelationBlockSavings.relation_seeded_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:51.444183+00:00
-- url     : https://prove2.me/theorems/5a526d62-85bd-4de5-80f6-45704589a60a
-- title:
--   Relation Block Savings: relation seeded bound
-- statement:
--   Savings from the relation survive adjoining all rules linked to its seeds.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L96-L119
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L96-L119

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSavings.relation_seeded_bound {t k : ℕ} (ht : 2 ≤ t) (U I : RuleSet k)
    (hIU : I ⊆ U) (hI : 2 ≤ I.card) (hcat : ∀ u ∈ U, CatalogueRule t k u)
    (hcover : ∀ u ∈ U, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) i u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount U ≤ (2 * t - 1) * U.card := by sorry
