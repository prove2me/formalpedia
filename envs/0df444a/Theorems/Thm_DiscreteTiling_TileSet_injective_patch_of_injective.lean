-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_injective_patch_of_injective
-- name    : DiscreteTiling.TileSet.injective_patch_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:16:44.625731+00:00
-- url     : https://prove2.me/theorems/bba7a269-bd9c-4b38-9425-874a7123913d
-- title:
--   Tile Set: injective patch of injective
-- statement:
--   The Tile Set construction uses the injective patch of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L153-L155
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L153-L155

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

theorem DiscreteTiling.TileSet.injective_patch_of_injective {t : TileSet ps ιₜ} (s : Set X) (ht : Injective t) :
    Injective (t.patch s) := by sorry
