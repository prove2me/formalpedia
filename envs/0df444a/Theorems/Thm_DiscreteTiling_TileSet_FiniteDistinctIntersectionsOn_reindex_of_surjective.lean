-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_FiniteDistinctIntersectionsOn_reindex_of_surjective
-- name    : DiscreteTiling.TileSet.FiniteDistinctIntersectionsOn.reindex_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:02:24.053627+00:00
-- url     : https://prove2.me/theorems/e2e7fd9b-167b-4edb-bb74-3aab1b353402
-- title:
--   Finite Distinct Intersections On: reindex of surjective
-- statement:
--   The Finite Distinct Intersections On construction uses the reindex of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L339-L344
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L339-L344

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

theorem DiscreteTiling.TileSet.FiniteDistinctIntersectionsOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ}
    {e : ιₜ' → ιₜ} (hfi : (t.reindex e).FiniteDistinctIntersectionsOn s) (h : Surjective e) :
    t.FiniteDistinctIntersectionsOn s := by sorry
