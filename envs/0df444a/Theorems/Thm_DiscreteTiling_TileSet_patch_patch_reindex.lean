-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_patch_patch_reindex
-- name    : DiscreteTiling.TileSet.patch_patch_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:14:20.64851+00:00
-- url     : https://prove2.me/theorems/ec6642c1-223f-4e59-a93d-61c5fc97451f
-- title:
--   Tile Set: patch patch reindex
-- statement:
--   The Tile Set construction uses the patch patch reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L240-L242
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L240-L242

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

theorem DiscreteTiling.TileSet.patch_patch_reindex (t : TileSet ps ιₜ) {s₁ s₂ : Set X} (h : s₂ ⊆ s₁) :
    (t.patch s₂).reindex (t.patchPatchEquiv h) = (t.patch s₁).patch s₂ := by sorry
