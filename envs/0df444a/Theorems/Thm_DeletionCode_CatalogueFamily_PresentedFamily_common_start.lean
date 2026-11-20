-- Prove2me | Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_common_start
-- name    : DeletionCode.CatalogueFamily.PresentedFamily.common_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:22:23.661073+00:00
-- url     : https://prove2.me/theorems/e3cbe411-476f-41b0-ad99-b7ed69003891
-- title:
--   Presented Family: common start
-- statement:
--   The Presented Family construction uses the common start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L118-L122
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean#L118-L122

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

theorem DeletionCode.CatalogueFamily.PresentedFamily.common_start (P : PresentedFamily t k R G) (b : Fin (2 * t * R)) :
    vertex P.E.family (windowLength k) b false 0 =
      vertex P.E.family (windowLength k) b true 0 := by sorry
