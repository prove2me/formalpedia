-- Prove2me | Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_gram_prefix_hasVertex
-- name    : DeletionCode.CatalogueFamily.PresentedFamily.gram_prefix_hasVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:22:18.068685+00:00
-- url     : https://prove2.me/theorems/9b5f8e68-07b2-4aeb-aca9-c41d65af0d67
-- title:
--   Presented Family: gram prefix has Vertex
-- statement:
--   The Presented Family construction uses the gram prefix has Vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L173-L180
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L173-L180

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

theorem DeletionCode.CatalogueFamily.PresentedFamily.gram_prefix_hasVertex (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) (g : Gram (windowLength k))
    (hg : HasGram P.E.family (windowLength k) b g) :
    HasVertex P.E.family (windowLength k) b (gramPrefix g) := by sorry
