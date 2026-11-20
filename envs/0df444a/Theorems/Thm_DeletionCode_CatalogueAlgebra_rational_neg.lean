-- Prove2me | Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
-- name    : DeletionCode.CatalogueAlgebra.rational_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:44.443801+00:00
-- url     : https://prove2.me/theorems/8ef0c870-3ea8-466e-8c3b-4e7f02586516
-- title:
--   Catalogue Algebra: rational neg
-- statement:
--   The Catalogue Algebra construction uses the rational neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean#L26-L28
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean#L26-L28

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_DeletionCode_CatalogueAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators

theorem DeletionCode.CatalogueAlgebra.rational_neg {L : ℕ} (u : Gram L → ℤ) : rational (-u) = -rational u := by sorry
