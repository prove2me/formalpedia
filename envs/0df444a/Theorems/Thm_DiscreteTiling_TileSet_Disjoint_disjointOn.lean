-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_Disjoint_disjointOn
-- name    : DiscreteTiling.TileSet.Disjoint.disjointOn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:01:20.900409+00:00
-- url     : https://prove2.me/theorems/6f773114-2c0f-4884-bc9a-5db1075d4052
-- title:
--   Disjoint: disjoint On
-- statement:
--   The Disjoint construction uses the disjoint On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L138-L140
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L138-L140

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

theorem DiscreteTiling.TileSet.Disjoint.disjointOn (s : Set X) {t : TileSet ps ιₜ} (hd : t.Disjoint) :
    t.DisjointOn s := by sorry
