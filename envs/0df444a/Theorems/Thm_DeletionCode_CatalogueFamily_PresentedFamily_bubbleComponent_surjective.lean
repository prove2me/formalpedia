-- Prove2me | Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_surjective
-- name    : DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:22:12.699605+00:00
-- url     : https://prove2.me/theorems/99685a52-af5a-45d7-8f19-5de986561ab6
-- title:
--   Presented Family: bubble Component surjective
-- statement:
--   The Presented Family construction uses the bubble Component surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L153-L163
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L153-L163

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_CatalogueFamily
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueFamily
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks
open scoped BigOperators
open DeletionCode.CatalogueFamily.PresentedFamily
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}

theorem DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_surjective (P : PresentedFamily t k R G) :
    Function.Surjective P.bubbleComponent := by sorry
