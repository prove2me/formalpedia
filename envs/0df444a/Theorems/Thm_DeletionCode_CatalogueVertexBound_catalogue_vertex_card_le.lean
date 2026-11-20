-- Prove2me | Theorems.Thm_DeletionCode_CatalogueVertexBound_catalogue_vertex_card_le
-- name    : DeletionCode.CatalogueVertexBound.catalogue_vertex_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:25.869736+00:00
-- url     : https://prove2.me/theorems/82d9b82c-ddfa-4826-bb34-a187cbbb8a7d
-- title:
--   Catalogue Vertex Bound: catalogue vertex card le
-- statement:
--   The finite vertex type is the actual incident-vertex set of the rule's
--   nonzero signed support, not a count attached to a chosen presentation.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueVertexBound.lean#L115-L130
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueVertexBound.lean#L115-L130

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

theorem DeletionCode.CatalogueVertexBound.catalogue_vertex_card_le {t k : ℕ}
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w) :
    Fintype.card (RuleSetVertex {w}) ≤ 4 * t * windowLength k := by sorry
