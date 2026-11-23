-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_union_patch
-- name    : DiscreteTiling.TileSet.union_patch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:17:15.144048+00:00
-- url     : https://prove2.me/theorems/97bf3608-8069-4fed-a4f9-f1bd7180a908
-- title:
--   Tile Set: union patch
-- statement:
--   The Tile Set construction uses the union patch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L223-L225
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L223-L225

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

theorem DiscreteTiling.TileSet.union_patch (t : TileSet ps ιₜ) (s : Set X) :
    ⋃ i, (t.patch s i : Set X) = ⋃ (i) (_ : (s ∩ t i).Nonempty), (t i : Set X) := by sorry
