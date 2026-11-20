-- Prove2me | Theorems.Thm_DeletionCode_RelationSavings_savings_from_relation
-- name    : DeletionCode.RelationSavings.savings_from_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:08.543174+00:00
-- url     : https://prove2.me/theorems/d06d9ff7-c89e-422c-97b7-06bc3b06db69
-- title:
--   Relation Savings: savings from relation
-- statement:
--   Manuscript savings-from-a-relation lemma on the actual finite rule set.
--   The statement holds even without the manuscript's independence and generation
--   assumptions. All participating coefficients must be nonzero.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSavings.lean#L109-L139
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSavings.lean#L109-L139

import Definitions.Def_DeletionCode_CatalogueFamily
import Definitions.Def_DeletionCode_ComponentFibers
import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_RelationSavings
set_option autoImplicit true
open DeletionCode DeletionCode.RelationSavings
open HeaderRecovery SignedSupport RuleReconstruction RuleSetGraph SupportComponents
open SignedRuleCount ConnectedBlocks CatalogueFamily ComponentFibers SupportInclusion
open scoped BigOperators
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}

theorem DeletionCode.RelationSavings.savings_from_relation (I : RuleSet k)
    (hcat : ∀ u ∈ I, CatalogueRule t k u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount I ≤ t * I.card + t := by sorry
