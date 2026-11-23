-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_FiniteIntersections_reindex_of_surjective
-- name    : DiscreteTiling.TileSet.FiniteIntersections.reindex_of_surjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:01:37.42305+00:00
-- url     : https://prove2.me/theorems/1dfa3619-5092-446b-acba-0dadd1bd5b7d
-- title:
--   Finite Intersections: reindex of surjective
-- statement:
--   The Finite Intersections construction uses the reindex of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L173-L176
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L173-L176

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

theorem DiscreteTiling.TileSet.FiniteIntersections.reindex_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteIntersections) (h : Surjective e) :
    t.FiniteIntersections := by sorry
