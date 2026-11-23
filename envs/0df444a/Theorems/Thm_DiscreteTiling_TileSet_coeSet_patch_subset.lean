-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_coeSet_patch_subset
-- name    : DiscreteTiling.TileSet.coeSet_patch_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:16:58.903336+00:00
-- url     : https://prove2.me/theorems/ea40f317-9aac-4d86-99c5-804826a550aa
-- title:
--   Tile Set: coe Set patch subset
-- statement:
--   The Tile Set construction uses the coe Set patch subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L176-L178
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L176-L178

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ ιₜ' Eᵤ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.coeSet_patch_subset (t : TileSet ps ιₜ) (s : Set X) :
    (t.patch s : Set (PlacedTile ps)) ⊆ t := by sorry
