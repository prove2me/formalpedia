-- Prove2me | Theorems.Thm_DiscreteTiling_TileSetCard_coe_mk
-- name    : DiscreteTiling.TileSetCard.coe_mk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:03:39.194537+00:00
-- url     : https://prove2.me/theorems/6f065778-cd95-4a5f-821b-212f865cdb6e
-- title:
--   Tile Set Card: coe mk
-- statement:
--   The Tile Set Card construction uses the coe mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L61-L61
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L61-L61

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Theorems.Thm_DiscreteTiling_TileSet_coe_mk

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

theorem DiscreteTiling.TileSetCard.coe_mk (t) : (⟨t⟩ : TileSetCard ps) = t := by sorry
