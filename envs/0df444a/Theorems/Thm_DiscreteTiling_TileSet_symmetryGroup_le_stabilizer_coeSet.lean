-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_le_stabilizer_coeSet
-- name    : DiscreteTiling.TileSet.symmetryGroup_le_stabilizer_coeSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:52:55.546918+00:00
-- url     : https://prove2.me/theorems/462974cf-d2d7-431a-b6f8-1cbdde6e5459
-- title:
--   Tile Set: symmetry Group le stabilizer coe Set
-- statement:
--   The Tile Set construction uses the symmetry Group le stabilizer coe Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L414-L419
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L414-L419

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

theorem DiscreteTiling.TileSet.symmetryGroup_le_stabilizer_coeSet (t : TileSet ps ιₜ) :
    t.symmetryGroup ≤ MulAction.stabilizer G (t : Set (PlacedTile ps)) := by sorry
