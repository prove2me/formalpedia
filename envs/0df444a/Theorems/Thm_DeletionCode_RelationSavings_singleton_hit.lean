-- Prove2me | Theorems.Thm_DeletionCode_RelationSavings_singleton_hit
-- name    : DeletionCode.RelationSavings.singleton_hit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:06.712517+00:00
-- url     : https://prove2.me/theorems/e21c60b9-a8df-409b-bcf4-a1dd462e5f83
-- title:
--   Relation Savings: singleton hit
-- statement:
--   Every singleton occurrence component is hit by an actual vertex of w.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSavings.lean#L74-L87
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSavings.lean#L74-L87

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

theorem DeletionCode.RelationSavings.singleton_hit (P : PresentedFamily t k R G)
    (w : Gram (windowLength k) → ℤ) (a : Fin R → ℚ)
    (hrel : RelationSupport.Relation G w a) (ha : ∀ r, a r ≠ 0)
    (C : RuleSetComponents (Finset.univ.image G))
    (hC : SingletonFiber P.bubbleComponent C) :
    ∃ v : RuleSetVertex {w},
      supportComponentMap (relation_support_included w a hrel)
        (Quotient.mk (ruleSetSetoid {w}) v) = C := by sorry
