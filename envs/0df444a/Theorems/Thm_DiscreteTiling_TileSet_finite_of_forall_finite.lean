-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_finite_of_forall_finite
-- name    : DiscreteTiling.TileSet.finite_of_forall_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:53:07.049183+00:00
-- url     : https://prove2.me/theorems/1bac4ae3-0b78-48f7-bc5d-6e57423f863a
-- title:
--   Tile Set: finite of forall finite
-- statement:
--   The Tile Set construction uses the finite of forall finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L130-L133
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L130-L133

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ι ιₜ ιₜ' ιₜ'' ιₜ''' E E' F : Type*} {ιₜι ιₜ'ι : ι → Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
open DiscreteTiling.TileSet
attribute [coe] tiles

theorem DiscreteTiling.TileSet.finite_of_forall_finite (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Finite)
    {pt : PlacedTile ps} (hpt : pt ∈ t) : (pt : Set X).Finite := by sorry
