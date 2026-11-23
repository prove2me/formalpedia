-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_IsTiling_finiteDistinctIntersections
-- name    : DiscreteTiling.TileSet.IsTiling.finiteDistinctIntersections
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:00:24.946795+00:00
-- url     : https://prove2.me/theorems/114d147c-4e15-4e6a-8780-e64301e94d2f
-- title:
--   Is Tiling: finite Distinct Intersections
-- statement:
--   The Is Tiling construction uses the finite Distinct Intersections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L118-L120
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L118-L120

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

theorem DiscreteTiling.TileSet.IsTiling.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : t.IsTiling) : t.FiniteDistinctIntersections := by sorry
