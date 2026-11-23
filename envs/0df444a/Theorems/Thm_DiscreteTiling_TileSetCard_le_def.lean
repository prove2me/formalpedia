-- Prove2me | Theorems.Thm_DiscreteTiling_TileSetCard_le_def
-- name    : DiscreteTiling.TileSetCard.le_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:55:57.090486+00:00
-- url     : https://prove2.me/theorems/fdfc4cf1-efbe-4528-b518-5f4efc4cc80d
-- title:
--   Tile Set Card: le def
-- statement:
--   The Tile Set Card construction uses the le def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L91-L92
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L91-L92

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

theorem DiscreteTiling.TileSetCard.le_def {t₁ t₂ : TileSetCard ps} : t₁ ≤ t₂ ↔ ∀ i, t₁ i ≤ t₂ i := by sorry
