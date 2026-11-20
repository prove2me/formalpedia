-- Prove2me | Theorems.Thm_DeletionCode_RelationSavings_singleton_coordinate
-- name    : DeletionCode.RelationSavings.singleton_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:06.879797+00:00
-- url     : https://prove2.me/theorems/cb0e86ea-0fd8-4045-a04a-ec1f20f7621d
-- title:
--   Relation Savings: singleton coordinate
-- statement:
--   A singleton occurrence component supplies a coordinate unique to its rule.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSavings.lean#L28-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSavings.lean#L28-L59

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

theorem DeletionCode.RelationSavings.singleton_coordinate (P : PresentedFamily t k R G)
    (C : RuleSetComponents (Finset.univ.image G))
    (hC : SingletonFiber P.bubbleComponent C) :
    ∃ r g, G r g ≠ 0 ∧ (∀ s, s ≠ r → G s g = 0) ∧
      ∃ hg : Incident (Finset.univ.image G) (gramPrefix g),
        Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨gramPrefix g, hg⟩ = C := by sorry
