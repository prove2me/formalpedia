-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_coeSet_reindex_eq_range_comp
-- name    : DiscreteTiling.TileSet.coeSet_reindex_eq_range_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:52:41.684703+00:00
-- url     : https://prove2.me/theorems/2d7b86ae-e5b9-40c0-b5a4-07666ba06cf1
-- title:
--   Tile Set: coe Set reindex eq range comp
-- statement:
--   The Tile Set construction uses the coe Set reindex eq range comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L198-L200
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L198-L200

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

theorem DiscreteTiling.TileSet.coeSet_reindex_eq_range_comp (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    (t.reindex f : Set (PlacedTile ps)) = Set.range (t ∘ f) := by sorry
