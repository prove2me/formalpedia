-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_mem_symmetryGroup_iff_exists
-- name    : DiscreteTiling.TileSet.mem_symmetryGroup_iff_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:51:41.597824+00:00
-- url     : https://prove2.me/theorems/c6a70731-7435-4af4-a23d-8242ac0b38b8
-- title:
--   Tile Set: mem symmetry Group iff exists
-- statement:
--   A group element is in the symmetry group if and only if there is a permutation of the indices
--   such that mapping by the group element and that permutation preserves the `TileSet`.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L329-L336
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L329-L336

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

theorem DiscreteTiling.TileSet.mem_symmetryGroup_iff_exists {t : TileSet ps ιₜ} {g : G} :
    g ∈ t.symmetryGroup ↔ ∃ f : Equiv.Perm ιₜ, (g • t).reindex f = t := by sorry
