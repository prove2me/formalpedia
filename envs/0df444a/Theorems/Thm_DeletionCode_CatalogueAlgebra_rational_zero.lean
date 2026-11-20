-- Prove2me | Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
-- name    : DeletionCode.CatalogueAlgebra.rational_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:44.227566+00:00
-- url     : https://prove2.me/theorems/838311f5-d1b0-41c6-af7c-3b47e083acea
-- title:
--   Catalogue Algebra: rational zero
-- statement:
--   The Catalogue Algebra construction uses the rational zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean#L22-L24
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean#L22-L24

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_DeletionCode_CatalogueAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators

theorem DeletionCode.CatalogueAlgebra.rational_zero {L : ℕ} : rational (0 : Gram L → ℤ) = 0 := by sorry
