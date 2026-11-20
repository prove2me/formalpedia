-- Prove2me | Theorems.Thm_DeletionCode_CatalogueBridge_differentLengths
-- name    : DeletionCode.CatalogueBridge.differentLengths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:13.676189+00:00
-- url     : https://prove2.me/theorems/521f1a2c-8419-4fbd-88fd-d660b7bdb296
-- title:
--   Catalogue Bridge: different Lengths
-- statement:
--   Header lengths alone already imply that the two paths have unequal numbers of windows.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean#L22-L29
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean#L22-L29

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount

theorem DeletionCode.CatalogueBridge.differentLengths {B : Type*} {k : ℕ} (E : EditedFamily B k) (b : B) :
    E.family.extra b false ≠ E.family.extra b true := by sorry
