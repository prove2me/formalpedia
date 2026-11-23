-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_DisjointOn_reindex_of_embeddingLike
-- name    : DiscreteTiling.TileSet.DisjointOn.reindex_of_embeddingLike
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:01:20.781737+00:00
-- url     : https://prove2.me/theorems/390c67d4-2edd-433d-ba23-e36e60bf3493
-- title:
--   Disjoint On: reindex of embedding Like
-- statement:
--   The Disjoint On construction uses the reindex of embedding Like property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L113-L115
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L113-L115

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

theorem DiscreteTiling.TileSet.DisjointOn.reindex_of_embeddingLike {s : Set X} {t : TileSet ps ιₜ}
    (hd : t.DisjointOn s) (e : F) : (t.reindex e).DisjointOn s := by sorry
