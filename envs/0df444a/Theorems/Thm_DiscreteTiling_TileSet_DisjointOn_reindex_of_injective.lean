-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_DisjointOn_reindex_of_injective
-- name    : DiscreteTiling.TileSet.DisjointOn.reindex_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:35.300365+00:00
-- url     : https://prove2.me/theorems/2cbe7a47-c50e-4136-aa21-79e7529fa665
-- title:
--   Disjoint On: reindex of injective
-- statement:
--   The Disjoint On construction uses the reindex of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L109-L111
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L109-L111

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

theorem DiscreteTiling.TileSet.DisjointOn.reindex_of_injective {s : Set X} {t : TileSet ps ιₜ} (hd : t.DisjointOn s)
    {e : ιₜ' → ιₜ} (h : Injective e) : (t.reindex e).DisjointOn s := by sorry
