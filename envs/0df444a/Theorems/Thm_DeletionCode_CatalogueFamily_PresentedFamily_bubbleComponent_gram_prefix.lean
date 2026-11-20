-- Prove2me | Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_gram_prefix
-- name    : DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_gram_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:22:13.358981+00:00
-- url     : https://prove2.me/theorems/ba91591f-5782-480c-87cf-3902a593a50c
-- title:
--   Presented Family: bubble Component gram prefix
-- statement:
--   The Presented Family construction uses the bubble Component gram prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L182-L188
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L182-L188

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

theorem DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_gram_prefix (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) (g : Gram (windowLength k))
    (hg : HasGram P.E.family (windowLength k) b g)
    (hv : Incident (Finset.univ.image G) (gramPrefix g)) :
    P.bubbleComponent b =
      Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨gramPrefix g, hv⟩ := by sorry
