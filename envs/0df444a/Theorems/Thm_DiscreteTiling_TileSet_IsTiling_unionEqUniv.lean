-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_IsTiling_unionEqUniv
-- name    : DiscreteTiling.TileSet.IsTiling.unionEqUniv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:58:31.271009+00:00
-- url     : https://prove2.me/theorems/a4a80959-9cc0-49c4-b60d-75c654b0dea6
-- title:
--   Is Tiling: union Eq Univ
-- statement:
--   The Is Tiling construction uses the union Eq Univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L102-L103
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L102-L103

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.IsTiling.unionEqUniv {t : TileSet ps ιₜ} (h : t.IsTiling) : t.UnionEqUniv := by sorry
