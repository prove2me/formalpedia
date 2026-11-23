-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_card_reindex_of_bijective
-- name    : DiscreteTiling.TileSet.card_reindex_of_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:56:37.465111+00:00
-- url     : https://prove2.me/theorems/7f9b1a42-ceff-42da-9f8b-87003d6b0d8e
-- title:
--   Tile Set: card reindex of bijective
-- statement:
--   The Tile Set construction uses the card reindex of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L132-L135
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L132-L135

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

theorem DiscreteTiling.TileSet.card_reindex_of_bijective (t : TileSet ps ιᵤ) {f : ιᵤ' → ιᵤ} (hf : Bijective f) :
    (t.reindex f).card = t.card := by sorry
