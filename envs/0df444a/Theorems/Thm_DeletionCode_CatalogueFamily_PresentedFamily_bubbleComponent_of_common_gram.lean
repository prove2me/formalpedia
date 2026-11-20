-- Prove2me | Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_of_common_gram
-- name    : DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_of_common_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:22:32.854652+00:00
-- url     : https://prove2.me/theorems/88b636ab-221e-48b9-a4b5-082aeb9d885a
-- title:
--   Presented Family: bubble Component of common gram
-- statement:
--   The Presented Family construction uses the bubble Component of common gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L190-L201
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L190-L201

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

theorem DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_of_common_gram (P : PresentedFamily t k R G)
    (a b : Fin (2 * t * R)) (g : Gram (windowLength k))
    (ha : HasGram P.E.family (windowLength k) a g)
    (hb : HasGram P.E.family (windowLength k) b g) :
    P.bubbleComponent a = P.bubbleComponent b := by sorry
