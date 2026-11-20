-- Prove2me | Theorems.Thm_DeletionCode_CatalogueVertexBound_namedVertex_surjective
-- name    : DeletionCode.CatalogueVertexBound.namedVertex_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:26.585373+00:00
-- url     : https://prove2.me/theorems/840e4a2e-6e89-404a-9d49-1b4724680b20
-- title:
--   Catalogue Vertex Bound: named Vertex surjective
-- statement:
--   The Catalogue Vertex Bound construction uses the named Vertex surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueVertexBound.lean#L31-L53
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueVertexBound.lean#L31-L53

import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CatalogueVertexBound
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueVertexBound
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport RuleReconstruction RuleSetGraph SupportComponents ConnectedBlocks
open scoped BigOperators

theorem DeletionCode.CatalogueVertexBound.namedVertex_surjective {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k) :
    Function.Surjective (namedVertex E) := by sorry
