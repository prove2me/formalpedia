-- Prove2me | Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_injective
-- name    : DeletionCode.CatalogueAlgebra.rational_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:47.752192+00:00
-- url     : https://prove2.me/theorems/108e988f-19d4-411e-aa09-da4febb49982
-- title:
--   Catalogue Algebra: rational injective
-- statement:
--   The Catalogue Algebra construction uses the rational injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean#L16-L20
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean#L16-L20

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_DeletionCode_CatalogueAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators

theorem DeletionCode.CatalogueAlgebra.rational_injective {L : ℕ} : Function.Injective (@rational L) := by sorry
