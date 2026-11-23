-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_IsTiling_finiteIntersections
-- name    : DiscreteTiling.TileSet.IsTiling.finiteIntersections
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:59:05.915803+00:00
-- url     : https://prove2.me/theorems/6d18a0bc-3015-4ddf-8886-b43c9c5d9623
-- title:
--   Is Tiling: finite Intersections
-- statement:
--   The Is Tiling construction uses the finite Intersections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L109-L111
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L109-L111

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Theorems.Thm_DiscreteTiling_TileSet_Disjoint_finiteIntersections

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

theorem DiscreteTiling.TileSet.IsTiling.finiteIntersections {t : TileSet ps ιₜ} (h : t.IsTiling) :
    t.FiniteIntersections := by sorry
