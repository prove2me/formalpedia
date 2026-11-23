-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_unionEqUniv_iff_unionEq
-- name    : DiscreteTiling.TileSet.unionEqUniv_iff_unionEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:06.037557+00:00
-- url     : https://prove2.me/theorems/1691c6aa-3ab5-4a4d-b9e1-2d733f9c98c6
-- title:
--   Tile Set: union Eq Univ iff union Eq
-- statement:
--   The Tile Set construction uses the union Eq Univ iff union Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L101-L102
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L101-L102

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

theorem DiscreteTiling.TileSet.unionEqUniv_iff_unionEq {t : TileSet ps ιₜ} : t.UnionEqUniv ↔ t.UnionEq Set.univ := by sorry
