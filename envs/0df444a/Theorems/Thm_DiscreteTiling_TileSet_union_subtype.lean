-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_union_subtype
-- name    : DiscreteTiling.TileSet.union_subtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:26.767056+00:00
-- url     : https://prove2.me/theorems/828dd5f1-ef08-4475-8b2c-cbb15a2b0c4f
-- title:
--   Tile Set: union subtype
-- statement:
--   The Tile Set construction uses the union subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L109-L112
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L109-L112

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

theorem DiscreteTiling.TileSet.union_subtype (t : TileSet ps ιₜ) (p : ιₜ → Prop) :
    ⋃ i, (t.subtype p i : Set X) = ⋃ (i) (_ : p i), (t i : Set X) := by sorry
