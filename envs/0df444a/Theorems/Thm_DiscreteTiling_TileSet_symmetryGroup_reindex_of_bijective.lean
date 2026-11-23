-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
-- name    : DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:51:31.267586+00:00
-- url     : https://prove2.me/theorems/96c65f5c-8b12-4453-9c9d-2b75100d508f
-- title:
--   Tile Set: symmetry Group reindex of bijective
-- statement:
--   The Tile Set construction uses the symmetry Group reindex of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L388-L390
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L388-L390

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

theorem DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective (t : TileSet ps ιₜ) {f : ιₜ' → ιₜ}
    (h : Bijective f) : (t.reindex f).symmetryGroup = t.symmetryGroup := by sorry
