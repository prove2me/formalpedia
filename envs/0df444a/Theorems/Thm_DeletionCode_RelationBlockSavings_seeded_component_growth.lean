-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSavings_seeded_component_growth
-- name    : DeletionCode.RelationBlockSavings.seeded_component_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:55.097365+00:00
-- url     : https://prove2.me/theorems/7e6e18c3-756f-47c1-9f05-6fb5f2ea338b
-- title:
--   Relation Block Savings: seeded component growth
-- statement:
--   The actual support-component increase when every retained rule is linked
--   to at least one seed rule by a path staying inside U.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L48-L93
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSavings.lean#L48-L93

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSavings.seeded_component_growth {t k : ℕ} (ht : 1 ≤ t) (U I : RuleSet k)
    (hIU : I ⊆ U) (hcat : ∀ w ∈ U, CatalogueRule t k w)
    (hcover : ∀ u ∈ U, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) i u) :
    componentCount U ≤ componentCount I + (2 * t - 1) * (U.card - I.card) := by sorry
