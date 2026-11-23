-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_reindex_sigma
-- name    : DiscreteTiling.TileSet.reindex_sigma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:53:39.818706+00:00
-- url     : https://prove2.me/theorems/3ff5544b-0c4b-4672-bb8b-8dbf729648d0
-- title:
--   Tile Set: reindex sigma
-- statement:
--   The Tile Set construction uses the reindex sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L468-L470
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L468-L470

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

theorem DiscreteTiling.TileSet.reindex_sigma (t : (i : ι) → TileSet ps (ιₜι i)) (f : (i : ι) → (ιₜ'ι i) → (ιₜι i)) :
    (TileSet.sigma t).reindex (Sigma.map id f) = TileSet.sigma fun i ↦ (t i).reindex (f i) := by sorry
