-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_patch_reindex_subtypeEquivRight
-- name    : DiscreteTiling.TileSet.patch_reindex_subtypeEquivRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:16:57.515928+00:00
-- url     : https://prove2.me/theorems/af3c53b9-f47b-4177-97da-ca33a72498bf
-- title:
--   Tile Set: patch reindex subtype Equiv Right
-- statement:
--   The Tile Set construction uses the patch reindex subtype Equiv Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L161-L164
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L161-L164

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

theorem DiscreteTiling.TileSet.patch_reindex_subtypeEquivRight (t : TileSet ps ιₜ) {s₁ s₂ : Set X}
    (h : ∀ i, (s₂ ∩ t i).Nonempty ↔ (s₁ ∩ t i).Nonempty) :
    (t.patch s₁).reindex (Equiv.subtypeEquivRight h) = t.patch s₂ := by sorry
