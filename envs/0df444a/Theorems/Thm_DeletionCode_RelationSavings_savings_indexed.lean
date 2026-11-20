-- Prove2me | Theorems.Thm_DeletionCode_RelationSavings_savings_indexed
-- name    : DeletionCode.RelationSavings.savings_indexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:09.320781+00:00
-- url     : https://prove2.me/theorems/5cd3d43b-3437-4cb7-9432-cb2ea759c2cb
-- title:
--   Relation Savings: savings indexed
-- statement:
--   Indexed form of the savings lemma; the bound counts the supplied labels.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSavings.lean#L90-L104
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSavings.lean#L90-L104

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

theorem DeletionCode.RelationSavings.savings_indexed (G : Fin R → Gram (windowLength k) → ℤ)
    (hcat : ∀ r, CatalogueRule t k (G r))
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : Fin R → ℚ) (ha : ∀ r, a r ≠ 0)
    (hrel : RelationSupport.Relation G w a) :
    componentCount (Finset.univ.image G) ≤ t * R + t := by sorry
