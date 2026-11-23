-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_unionEqUniv_iff
-- name    : DiscreteTiling.TileSet.unionEqUniv_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:12.392175+00:00
-- url     : https://prove2.me/theorems/f8848047-62d1-477f-8559-90bbea5cb339
-- title:
--   Tile Set: union Eq Univ iff
-- statement:
--   The Tile Set construction uses the union Eq Univ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L94-L95
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L94-L95

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

theorem DiscreteTiling.TileSet.unionEqUniv_iff {t : TileSet ps ιₜ} : t.UnionEqUniv ↔ (⋃ i, (t i : Set X)) = Set.univ := by sorry
