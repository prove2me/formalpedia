-- Prove2me | Theorems.Thm_DeletionCode_CatalogueVertexBound_supported_vertex_count_le
-- name    : DeletionCode.CatalogueVertexBound.supported_vertex_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:34.264163+00:00
-- url     : https://prove2.me/theorems/9387cf0a-4a1f-4009-a848-8f60abc17e93
-- title:
--   Catalogue Vertex Bound: supported vertex count le
-- statement:
--   The Catalogue Vertex Bound construction uses the supported vertex count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueVertexBound.lean#L66-L88
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueVertexBound.lean#L66-L88

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

theorem DeletionCode.CatalogueVertexBound.supported_vertex_count_le {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k) :
    Nat.card (SupportedVertex E.family (windowLength k)) ≤ 4 * t * windowLength k := by sorry
