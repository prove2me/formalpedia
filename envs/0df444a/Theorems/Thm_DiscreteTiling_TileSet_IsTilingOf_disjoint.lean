-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_IsTilingOf_disjoint
-- name    : DiscreteTiling.TileSet.IsTilingOf.disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:58:03.856745+00:00
-- url     : https://prove2.me/theorems/e49a978d-da0c-447b-960f-736720c23142
-- title:
--   Is Tiling Of: disjoint
-- statement:
--   The Is Tiling Of construction uses the disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L54-L56
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L54-L56

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

theorem DiscreteTiling.TileSet.IsTilingOf.disjoint {t : TileSet ps ιₜ} {s : Set X} (h : t.IsTilingOf s) :
    t.Disjoint := by sorry
