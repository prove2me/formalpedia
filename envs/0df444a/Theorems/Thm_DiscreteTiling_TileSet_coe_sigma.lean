-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
-- name    : DiscreteTiling.TileSet.coe_sigma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:51:26.813029+00:00
-- url     : https://prove2.me/theorems/1871d682-5dd8-4ebb-8755-cc1ccd756754
-- title:
--   Tile Set: coe sigma
-- statement:
--   The Tile Set construction uses the coe sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L456-L458
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L456-L458

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

theorem DiscreteTiling.TileSet.coe_sigma (t : (i : ι) → TileSet ps (ιₜι i)) :
    TileSet.sigma t = Sigma.uncurry (fun i ↦ ↑(t i)) := by sorry

attribute [defeq] DiscreteTiling.TileSet.coe_sigma
