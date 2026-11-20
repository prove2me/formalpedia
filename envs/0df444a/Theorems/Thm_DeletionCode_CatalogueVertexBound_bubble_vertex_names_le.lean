-- Prove2me | Theorems.Thm_DeletionCode_CatalogueVertexBound_bubble_vertex_names_le
-- name    : DeletionCode.CatalogueVertexBound.bubble_vertex_names_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:32.042551+00:00
-- url     : https://prove2.me/theorems/ec06362d-4746-4300-95d5-77caef2cde9e
-- title:
--   Catalogue Vertex Bound: bubble vertex names le
-- statement:
--   The two path lengths and rho ≥ 1 give at most 2L vertex names per bubble.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueVertexBound.lean#L56-L64
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueVertexBound.lean#L56-L64

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

theorem DeletionCode.CatalogueVertexBound.bubble_vertex_names_le {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k)
    (b : Fin (2 * t)) :
    E.family.extra b false + 2 + (E.family.extra b true + 1) ≤ 2 * windowLength k := by sorry
