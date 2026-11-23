-- Prove2me | Theorems.Thm_DiscreteTiling_TileSetCard_coe_sup
-- name    : DiscreteTiling.TileSetCard.coe_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:56:17.297058+00:00
-- url     : https://prove2.me/theorems/ccb1936c-ab7a-4578-bbfd-6e943d065381
-- title:
--   Tile Set Card: coe sup
-- statement:
--   The Tile Set Card construction uses the coe sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L74-L76
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L74-L76

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

theorem DiscreteTiling.TileSetCard.coe_sup (t₁ t₂ : TileSetCard ps) :
    (t₁ ⊔ t₂ : TileSetCard ps) = (t₁ : PlacedTile ps → Cardinal) ⊔ ↑t₂ := by sorry
