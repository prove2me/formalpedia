-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_card_patch_union
-- name    : DiscreteTiling.TileSet.card_patch_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:17:18.763808+00:00
-- url     : https://prove2.me/theorems/f52ab9d3-9a25-44b4-8cbe-577a9bbf8755
-- title:
--   Tile Set: card patch union
-- statement:
--   The Tile Set construction uses the card patch union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L249-L272
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L249-L272

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

theorem DiscreteTiling.TileSet.card_patch_union (t : TileSet ps ιₜ) (s₁ s₂ : Set X) :
    (t.patch (s₁ ∪ s₂)).card = (t.patch s₁).card ⊔ (t.patch s₂).card := by sorry
