-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_card_subtype_le
-- name    : DiscreteTiling.TileSet.card_subtype_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:14:02.281541+00:00
-- url     : https://prove2.me/theorems/ca1e1ca8-e585-4be0-b6f4-9645ebd6678b
-- title:
--   Tile Set: card subtype le
-- statement:
--   The Tile Set construction uses the card subtype le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L92-L93
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L92-L93

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

theorem DiscreteTiling.TileSet.card_subtype_le (t : TileSet ps ιₜ) (p : ιₜ → Prop) : (t.subtype p).card ≤ t.card := by sorry
