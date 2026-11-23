-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_smul_sum
-- name    : DiscreteTiling.TileSet.smul_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:53:34.660733+00:00
-- url     : https://prove2.me/theorems/5fa97814-5a01-457b-9c2d-145280d7ca2a
-- title:
--   Tile Set: smul sum
-- statement:
--   The Tile Set construction uses the smul sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L448-L450
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L448-L450

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

theorem DiscreteTiling.TileSet.smul_sum (g : G) (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ') :
    g • (t.sum t') = (g • t).sum (g • t') := by sorry
