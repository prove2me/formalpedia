-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isTiling_iff_of_injective
-- name    : DiscreteTiling.TileSet.isTiling_iff_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:09:48.305693+00:00
-- url     : https://prove2.me/theorems/cb52653e-0ab2-4cdd-acfc-5bd7847a0bae
-- title:
--   Tile Set: is Tiling iff of injective
-- statement:
--   The Tile Set construction uses the is Tiling iff of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L93-L97
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L93-L97

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.isTiling_iff_of_injective {t : TileSet ps ιₜ} (h : Injective t) :
    t.IsTiling ↔ ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ∧
      (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by sorry
