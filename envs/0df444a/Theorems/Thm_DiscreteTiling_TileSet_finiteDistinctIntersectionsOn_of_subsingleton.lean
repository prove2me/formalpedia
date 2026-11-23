-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_of_subsingleton
-- name    : DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_of_subsingleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:22.686847+00:00
-- url     : https://prove2.me/theorems/b4b48e25-ad2e-4312-88f8-8d4a088576bb
-- title:
--   Tile Set: finite Distinct Intersections On of subsingleton
-- statement:
--   The Tile Set construction uses the finite Distinct Intersections On of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L358-L360
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L358-L360

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

theorem DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_of_subsingleton [Subsingleton ιₜ] (s : Set X)
    (t : TileSet ps ιₜ) : t.FiniteDistinctIntersectionsOn s := by sorry
