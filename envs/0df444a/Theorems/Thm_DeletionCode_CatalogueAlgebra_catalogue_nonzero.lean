-- Prove2me | Theorems.Thm_DeletionCode_CatalogueAlgebra_catalogue_nonzero
-- name    : DeletionCode.CatalogueAlgebra.catalogue_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:45.97238+00:00
-- url     : https://prove2.me/theorems/5af3196d-5c00-40d8-a374-56450177ccce
-- title:
--   Catalogue Algebra: catalogue nonzero
-- statement:
--   The Catalogue Algebra construction uses the catalogue nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean#L41-L57
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean#L41-L57

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_DeletionCode_CatalogueAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators

theorem DeletionCode.CatalogueAlgebra.catalogue_nonzero {t k : ℕ} (ht : 1 ≤ t)
    (u : Gram (windowLength k) → ℤ) (hu : CatalogueRule t k u) : u ≠ 0 := by sorry
