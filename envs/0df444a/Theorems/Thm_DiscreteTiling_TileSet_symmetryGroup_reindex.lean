-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
-- name    : DiscreteTiling.TileSet.symmetryGroup_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:51:24.011994+00:00
-- url     : https://prove2.me/theorems/47462110-a277-45df-8264-8d5d52b83e96
-- title:
--   Tile Set: symmetry Group reindex
-- statement:
--   The Tile Set construction uses the symmetry Group reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L376-L386
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L376-L386

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

theorem DiscreteTiling.TileSet.symmetryGroup_reindex (t : TileSet ps ιₜ) (f : E) :
    (t.reindex f).symmetryGroup = t.symmetryGroup := by sorry
