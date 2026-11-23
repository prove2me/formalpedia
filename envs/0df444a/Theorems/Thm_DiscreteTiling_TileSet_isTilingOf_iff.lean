-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isTilingOf_iff
-- name    : DiscreteTiling.TileSet.isTilingOf_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:58:00.045796+00:00
-- url     : https://prove2.me/theorems/b3fe0bf5-6ac8-41ef-9276-025708b8e8ff
-- title:
--   Tile Set: is Tiling Of iff
-- statement:
--   The Tile Set construction uses the is Tiling Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L46-L48
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L46-L48

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

theorem DiscreteTiling.TileSet.isTilingOf_iff {t : TileSet ps ιₜ} {s : Set X} : t.IsTilingOf s ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = s := by sorry
