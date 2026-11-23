-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_card_eq_iff_exists_reindex_eq
-- name    : DiscreteTiling.TileSet.card_eq_iff_exists_reindex_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:09:00.796386+00:00
-- url     : https://prove2.me/theorems/2fdc470c-4a5b-445d-9040-decf45f6d577
-- title:
--   Tile Set: card eq iff exists reindex eq
-- statement:
--   The Tile Set construction uses the card eq iff exists reindex eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L140-L147
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L140-L147

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

theorem DiscreteTiling.TileSet.card_eq_iff_exists_reindex_eq {t₁ : TileSet ps ιᵤ} {t₂ : TileSet ps ιᵤ'} :
    t₁.card = t₂.card ↔ ∃ e : ιᵤ' ≃ ιᵤ, t₁.reindex e = t₂ := by sorry
