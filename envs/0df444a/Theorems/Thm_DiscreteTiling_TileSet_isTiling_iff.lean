-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isTiling_iff
-- name    : DiscreteTiling.TileSet.isTiling_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:00:03.550315+00:00
-- url     : https://prove2.me/theorems/17501c66-96e2-42c9-ac33-cefadbe85b39
-- title:
--   Tile Set: is Tiling iff
-- statement:
--   The Tile Set construction uses the is Tiling iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L86-L88
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L86-L88

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

theorem DiscreteTiling.TileSet.isTiling_iff {t : TileSet ps ιₜ} : t.IsTiling ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = Set.univ := by sorry
