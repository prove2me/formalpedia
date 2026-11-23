-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_FiniteIntersections_reindex_of_injective
-- name    : DiscreteTiling.TileSet.FiniteIntersections.reindex_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:37.11309+00:00
-- url     : https://prove2.me/theorems/f5bc5193-21a9-42ea-8acd-783b44dd5cf5
-- title:
--   Finite Intersections: reindex of injective
-- statement:
--   The Finite Intersections construction uses the reindex of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L164-L167
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L164-L167

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

theorem DiscreteTiling.TileSet.FiniteIntersections.reindex_of_injective {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) {e : ιₜ' → ιₜ} (h : Injective e) :
    (t.reindex e).FiniteIntersections := by sorry
