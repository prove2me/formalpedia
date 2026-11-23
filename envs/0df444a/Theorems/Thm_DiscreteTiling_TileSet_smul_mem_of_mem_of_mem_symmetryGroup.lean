-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_smul_mem_of_mem_of_mem_symmetryGroup
-- name    : DiscreteTiling.TileSet.smul_mem_of_mem_of_mem_symmetryGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:52:50.610152+00:00
-- url     : https://prove2.me/theorems/2d140b62-a367-4369-a754-8b6c2175a79f
-- title:
--   Tile Set: smul mem of mem of mem symmetry Group
-- statement:
--   If `g` is in the symmetry group, the image of any tile under `g` is in `t`.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L356-L360
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L356-L360

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

theorem DiscreteTiling.TileSet.smul_mem_of_mem_of_mem_symmetryGroup {t : TileSet ps ιₜ} {g : G} {pt : PlacedTile ps}
    (hg : g ∈ t.symmetryGroup) (hpt : pt ∈ t) : g • pt ∈ t := by sorry
