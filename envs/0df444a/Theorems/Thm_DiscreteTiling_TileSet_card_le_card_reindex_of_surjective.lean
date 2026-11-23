-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_card_le_card_reindex_of_surjective
-- name    : DiscreteTiling.TileSet.card_le_card_reindex_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:56:35.864499+00:00
-- url     : https://prove2.me/theorems/d6161ef8-e01f-4f33-8ff6-6b8544206c52
-- title:
--   Tile Set: card le card reindex of surjective
-- statement:
--   The Tile Set construction uses the card le card reindex of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L126-L130
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L126-L130

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ E F : Type*}
universe u v
variable {ιᵤ ιᵤ' : Type u} [EquivLike E ιᵤ' ιᵤ] [FunLike F ιᵤ' ιᵤ] [EmbeddingLike F ιᵤ' ιᵤ]
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.card_le_card_reindex_of_surjective (t : TileSet ps ιᵤ) {f : ιᵤ' → ιᵤ} (hf : Surjective f) :
    t.card ≤ (t.reindex f).card := by sorry
