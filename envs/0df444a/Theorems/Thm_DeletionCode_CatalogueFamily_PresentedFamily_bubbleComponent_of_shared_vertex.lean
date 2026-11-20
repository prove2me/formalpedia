-- Prove2me | Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_of_shared_vertex
-- name    : DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_of_shared_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:22:14.380407+00:00
-- url     : https://prove2.me/theorems/f3d01eac-3719-4aec-bf3b-74986b6e00b8
-- title:
--   Presented Family: bubble Component of shared vertex
-- statement:
--   The Presented Family construction uses the bubble Component of shared vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L165-L171
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L165-L171

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

theorem DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_of_shared_vertex (P : PresentedFamily t k R G)
    (a b : Fin (2 * t * R)) (v : Vertex (windowLength k))
    (ha : HasVertex P.E.family (windowLength k) a v)
    (hb : HasVertex P.E.family (windowLength k) b v) :
    P.bubbleComponent a = P.bubbleComponent b := by sorry
