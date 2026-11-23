-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_finiteIntersections_iff
-- name    : DiscreteTiling.TileSet.finiteIntersections_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:01:21.226857+00:00
-- url     : https://prove2.me/theorems/90760181-7dbc-45b3-b0d1-6714a5a605e3
-- title:
--   Tile Set: finite Intersections iff
-- statement:
--   The Tile Set construction uses the finite Intersections iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L160-L162
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L160-L162

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Logic.Equiv.Pairwise
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' F : Type*}
variable [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.finiteIntersections_iff {t : TileSet ps ιₜ} :
    t.FiniteIntersections ↔ ∀ x, {i | x ∈ t i}.Finite := by sorry
