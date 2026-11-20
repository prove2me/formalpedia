-- Prove2me | Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_component_count
-- name    : DeletionCode.CatalogueFamily.PresentedFamily.component_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:22:22.376353+00:00
-- url     : https://prove2.me/theorems/2f0857e4-e94e-4480-9e7c-92523d7bc0db
-- title:
--   Presented Family: component count
-- statement:
--   The intrinsic signed-support count equals the component count of the constructed words.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L107-L111
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L107-L111

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

theorem DeletionCode.CatalogueFamily.PresentedFamily.component_count (P : PresentedFamily t k R G) :
    componentCount (Finset.univ.image G) =
      Fintype.card (GraphComponents P.E.family (windowLength k)) := by sorry
