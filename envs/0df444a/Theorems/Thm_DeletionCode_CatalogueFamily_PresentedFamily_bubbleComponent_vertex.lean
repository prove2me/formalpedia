-- Prove2me | Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_vertex
-- name    : DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:22:07.276675+00:00
-- url     : https://prove2.me/theorems/abe757da-1155-47b5-bf29-0ccca4b63f70
-- title:
--   Presented Family: bubble Component vertex
-- statement:
--   Every vertex on a bubble has the intrinsic component assigned to that bubble.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L139-L151
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L139-L151

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

theorem DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_vertex (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) (v : Vertex (windowLength k))
    (hv : Incident (Finset.univ.image G) v)
    (hhas : HasVertex P.E.family (windowLength k) b v) :
    P.bubbleComponent b = Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨v, hv⟩ := by sorry
