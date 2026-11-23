-- Prove2me | Theorems.Thm_DiscreteTiling_TileSetCard_coe_inf
-- name    : DiscreteTiling.TileSetCard.coe_inf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:04:03.461658+00:00
-- url     : https://prove2.me/theorems/d56e24c2-3e03-425c-a158-83352a3c15d9
-- title:
--   Tile Set Card: coe inf
-- statement:
--   The Tile Set Card construction uses the coe inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L81-L83
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L81-L83

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
open DiscreteTiling.TileSetCard
attribute [coe] tilesCard

theorem DiscreteTiling.TileSetCard.coe_inf (t₁ t₂ : TileSetCard ps) :
    (t₁ ⊓ t₂ : TileSetCard ps) = (t₁ : PlacedTile ps → Cardinal) ⊓ ↑t₂ := by sorry
