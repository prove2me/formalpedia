-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_Disjoint_reindex_of_injective
-- name    : DiscreteTiling.TileSet.Disjoint.reindex_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:30.148912+00:00
-- url     : https://prove2.me/theorems/9eb783ff-ae42-443b-8b6d-d5d9ad95a301
-- title:
--   Disjoint: reindex of injective
-- statement:
--   The Disjoint construction uses the reindex of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L70-L72
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L70-L72

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

theorem DiscreteTiling.TileSet.Disjoint.reindex_of_injective {t : TileSet ps ιₜ} (hd : t.Disjoint) {e : ιₜ' → ιₜ}
    (h : Injective e) : (t.reindex e).Disjoint := by sorry
