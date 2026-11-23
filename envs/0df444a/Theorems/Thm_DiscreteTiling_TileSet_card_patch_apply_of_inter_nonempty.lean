-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_card_patch_apply_of_inter_nonempty
-- name    : DiscreteTiling.TileSet.card_patch_apply_of_inter_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:14:19.736657+00:00
-- url     : https://prove2.me/theorems/e68a5efb-7405-46d2-87de-d0116d282e57
-- title:
--   Tile Set: card patch apply of inter nonempty
-- statement:
--   The Tile Set construction uses the card patch apply of inter nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L135-L143
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L135-L143

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

theorem DiscreteTiling.TileSet.card_patch_apply_of_inter_nonempty (t : TileSet ps ιₜ) {s : Set X} {pt : PlacedTile ps}
    (h : (s ∩ pt).Nonempty) : (t.patch s).card pt = #(↑t ⁻¹' {pt}) := by sorry
