-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_Disjoint_reindex_of_embeddingLike
-- name    : DiscreteTiling.TileSet.Disjoint.reindex_of_embeddingLike
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:01:08.361804+00:00
-- url     : https://prove2.me/theorems/39347ce3-0b0a-4482-ba6c-76255fe18796
-- title:
--   Disjoint: reindex of embedding Like
-- statement:
--   The Disjoint construction uses the reindex of embedding Like property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L74-L76
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L74-L76

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

theorem DiscreteTiling.TileSet.Disjoint.reindex_of_embeddingLike {t : TileSet ps ιₜ} (hd : t.Disjoint) (e : F) :
    (t.reindex e).Disjoint := by sorry
