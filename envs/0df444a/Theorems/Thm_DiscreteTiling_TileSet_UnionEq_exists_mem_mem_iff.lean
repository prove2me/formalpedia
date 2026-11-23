-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_UnionEq_exists_mem_mem_iff
-- name    : DiscreteTiling.TileSet.UnionEq.exists_mem_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:01.9378+00:00
-- url     : https://prove2.me/theorems/67102157-5f75-4cb2-9913-6a2d41c8d6be
-- title:
--   Union Eq: exists mem mem iff
-- statement:
--   The Union Eq construction uses the exists mem mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L67-L70
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L67-L70

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' : Type*}
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.UnionEq.exists_mem_mem_iff {t : TileSet ps ιₜ} {s : Set X} (h : t.UnionEq s) {x : X} :
    (∃ pt ∈ t, x ∈ pt) ↔ x ∈ s := by sorry
