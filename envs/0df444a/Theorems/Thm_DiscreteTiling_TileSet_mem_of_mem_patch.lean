-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_mem_of_mem_patch
-- name    : DiscreteTiling.TileSet.mem_of_mem_patch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:16:59.968992+00:00
-- url     : https://prove2.me/theorems/3c18d992-37ae-4937-a39e-30ec09dda6b2
-- title:
--   Tile Set: mem of mem patch
-- statement:
--   The Tile Set construction uses the mem of mem patch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L180-L182
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L180-L182

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

theorem DiscreteTiling.TileSet.mem_of_mem_patch {t : TileSet ps ιₜ} {s : Set X} {pt : PlacedTile ps} (h : pt ∈ t.patch s) :
    pt ∈ t := by sorry
