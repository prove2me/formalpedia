-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_union_of_mem_eq_iUnion
-- name    : DiscreteTiling.TileSet.union_of_mem_eq_iUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:51:44.072593+00:00
-- url     : https://prove2.me/theorems/5991c9c6-eb8e-4e31-b9ab-0e152d2144d1
-- title:
--   Tile Set: union of mem eq i Union
-- statement:
--   The Tile Set construction uses the union of mem eq i Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L113-L115
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L113-L115

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

theorem DiscreteTiling.TileSet.union_of_mem_eq_iUnion (t : TileSet ps ιₜ) : ⋃ pt ∈ t, (pt : Set X) = ⋃ i, (t i : Set X) := by sorry
