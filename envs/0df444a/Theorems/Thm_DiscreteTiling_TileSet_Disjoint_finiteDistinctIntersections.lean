-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_Disjoint_finiteDistinctIntersections
-- name    : DiscreteTiling.TileSet.Disjoint.finiteDistinctIntersections
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:31.78709+00:00
-- url     : https://prove2.me/theorems/a63c2f06-81d3-4314-af00-dd227df8d420
-- title:
--   Disjoint: finite Distinct Intersections
-- statement:
--   The Disjoint construction uses the finite Distinct Intersections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L306-L308
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L306-L308

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Logic.Equiv.Pairwise
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' F : Type*}
variable [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.Disjoint.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : t.Disjoint) : t.FiniteDistinctIntersections := by sorry
