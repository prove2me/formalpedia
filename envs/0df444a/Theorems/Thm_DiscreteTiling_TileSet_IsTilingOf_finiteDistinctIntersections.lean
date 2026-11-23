-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_IsTilingOf_finiteDistinctIntersections
-- name    : DiscreteTiling.TileSet.IsTilingOf.finiteDistinctIntersections
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:00:33.574961+00:00
-- url     : https://prove2.me/theorems/a0cae8aa-93bc-4de5-99a8-0ef74ebab6ca
-- title:
--   Is Tiling Of: finite Distinct Intersections
-- statement:
--   The Is Tiling Of construction uses the finite Distinct Intersections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L114-L116
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L114-L116

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Theorems.Thm_DiscreteTiling_TileSet_Disjoint_finiteDistinctIntersections

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

theorem DiscreteTiling.TileSet.IsTilingOf.finiteDistinctIntersections {t : TileSet ps ιₜ} {s : Set X}
    (h : t.IsTilingOf s) : t.FiniteDistinctIntersections := by sorry
