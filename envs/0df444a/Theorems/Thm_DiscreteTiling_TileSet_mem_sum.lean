-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_mem_sum
-- name    : DiscreteTiling.TileSet.mem_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:51:35.383727+00:00
-- url     : https://prove2.me/theorems/f9be37c1-d547-4cfc-9dbf-40291ba3c033
-- title:
--   Tile Set: mem sum
-- statement:
--   The Tile Set construction uses the mem sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L440-L442
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L440-L442

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

theorem DiscreteTiling.TileSet.mem_sum {pt : PlacedTile ps} {t : TileSet ps ιₜ} {t' : TileSet ps ιₜ'} :
    pt ∈ t.sum t' ↔ pt ∈ t ∨ pt ∈ t' := by sorry
