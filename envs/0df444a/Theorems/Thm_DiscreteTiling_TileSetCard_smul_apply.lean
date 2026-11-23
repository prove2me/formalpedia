-- Prove2me | Theorems.Thm_DiscreteTiling_TileSetCard_smul_apply
-- name    : DiscreteTiling.TileSetCard.smul_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:56:33.284096+00:00
-- url     : https://prove2.me/theorems/2d9d2333-5383-40f6-b4b1-5c8fe7f13b09
-- title:
--   Tile Set Card: smul apply
-- statement:
--   The Tile Set Card construction uses the smul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L104-L105
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean#L104-L105

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

theorem DiscreteTiling.TileSetCard.smul_apply (g : G) (t : TileSetCard ps) (pt : PlacedTile ps) : (g • t) pt = t (g⁻¹ • pt) := by sorry
