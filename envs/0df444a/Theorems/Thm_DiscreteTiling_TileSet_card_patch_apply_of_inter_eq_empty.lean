-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_card_patch_apply_of_inter_eq_empty
-- name    : DiscreteTiling.TileSet.card_patch_apply_of_inter_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:14:20.754112+00:00
-- url     : https://prove2.me/theorems/e33e8421-ac19-4e38-817b-07cbd99bae5a
-- title:
--   Tile Set: card patch apply of inter eq empty
-- statement:
--   The Tile Set construction uses the card patch apply of inter eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L145-L151
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L145-L151

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

theorem DiscreteTiling.TileSet.card_patch_apply_of_inter_eq_empty (t : TileSet ps ιₜ) {s : Set X} {pt : PlacedTile ps}
    (h : (s ∩ pt) = ∅) : (t.patch s).card pt = 0 := by sorry
