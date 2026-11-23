-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_IsTilingOf_finiteIntersections
-- name    : DiscreteTiling.TileSet.IsTilingOf.finiteIntersections
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:59:11.335801+00:00
-- url     : https://prove2.me/theorems/e0b9e777-c203-4cd7-8da4-1de1b8e6864e
-- title:
--   Is Tiling Of: finite Intersections
-- statement:
--   The Is Tiling Of construction uses the finite Intersections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L105-L107
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L105-L107

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

theorem DiscreteTiling.TileSet.IsTilingOf.finiteIntersections {t : TileSet ps ιₜ} {s : Set X} (h : t.IsTilingOf s) :
    t.FiniteIntersections := by sorry
