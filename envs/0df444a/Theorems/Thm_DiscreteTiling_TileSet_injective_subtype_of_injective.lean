-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_injective_subtype_of_injective
-- name    : DiscreteTiling.TileSet.injective_subtype_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:30.353581+00:00
-- url     : https://prove2.me/theorems/0c6dfd45-764f-4c17-9c23-067cf75c411d
-- title:
--   Tile Set: injective subtype of injective
-- statement:
--   The Tile Set construction uses the injective subtype of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L59-L61
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L59-L61

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

theorem DiscreteTiling.TileSet.injective_subtype_of_injective {t : TileSet ps ιₜ} (p : ιₜ → Prop) (ht : Injective t) :
    Injective (t.subtype p) := by sorry
