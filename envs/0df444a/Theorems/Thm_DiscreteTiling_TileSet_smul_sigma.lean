-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_smul_sigma
-- name    : DiscreteTiling.TileSet.smul_sigma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:53:39.644738+00:00
-- url     : https://prove2.me/theorems/35ff3d6e-cd96-4a25-b586-70f31deeef3e
-- title:
--   Tile Set: smul sigma
-- statement:
--   The Tile Set construction uses the smul sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L472-L474
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L472-L474

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

theorem DiscreteTiling.TileSet.smul_sigma (g : G) (t : (i : ι) → TileSet ps (ιₜι i)) :
    g • TileSet.sigma t = TileSet.sigma (g • t) := by sorry
