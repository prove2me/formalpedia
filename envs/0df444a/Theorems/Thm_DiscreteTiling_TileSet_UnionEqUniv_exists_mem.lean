-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_UnionEqUniv_exists_mem
-- name    : DiscreteTiling.TileSet.UnionEqUniv.exists_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:09:19.629807+00:00
-- url     : https://prove2.me/theorems/318f6d1c-81c9-48d5-87ff-43287b464d40
-- title:
--   Union Eq Univ: exists mem
-- statement:
--   The Union Eq Univ construction uses the exists mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L104-L108
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L104-L108

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

theorem DiscreteTiling.TileSet.UnionEqUniv.exists_mem {t : TileSet ps ιₜ} (h : t.UnionEqUniv) (x : X) :
    ∃ i, x ∈ t i := by sorry
