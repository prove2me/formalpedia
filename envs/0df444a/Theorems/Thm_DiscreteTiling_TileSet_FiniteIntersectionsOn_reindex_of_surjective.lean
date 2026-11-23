-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_FiniteIntersectionsOn_reindex_of_surjective
-- name    : DiscreteTiling.TileSet.FiniteIntersectionsOn.reindex_of_surjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:01:44.636549+00:00
-- url     : https://prove2.me/theorems/cdd496ee-e4a4-451e-8343-579e0ce6790e
-- title:
--   Finite Intersections On: reindex of surjective
-- statement:
--   The Finite Intersections On construction uses the reindex of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L216-L219
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L216-L219

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

theorem DiscreteTiling.TileSet.FiniteIntersectionsOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteIntersectionsOn s) (h : Surjective e) :
    t.FiniteIntersectionsOn s := by sorry
