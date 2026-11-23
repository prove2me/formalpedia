-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_card_patch_le
-- name    : DiscreteTiling.TileSet.card_patch_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:14:15.253719+00:00
-- url     : https://prove2.me/theorems/5a19a8c3-25ce-45e2-a460-c90bc9029f55
-- title:
--   Tile Set: card patch le
-- statement:
--   The Tile Set construction uses the card patch le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L206-L207
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L206-L207

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

theorem DiscreteTiling.TileSet.card_patch_le (t : TileSet ps ιₜ) (s : Set X) : (t.patch s).card ≤ t.card := by sorry
