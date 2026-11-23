-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_unionEq_smul_tileSet_iff
-- name    : DiscreteTiling.TileSet.unionEq_smul_tileSet_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:09:11.923533+00:00
-- url     : https://prove2.me/theorems/289f6141-22ec-418a-8058-8a8c8caa4272
-- title:
--   Tile Set: union Eq smul tile Set iff
-- statement:
--   The Tile Set construction uses the union Eq smul tile Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L82-L86
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L82-L86

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

theorem DiscreteTiling.TileSet.unionEq_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    (g • t).UnionEq s ↔ t.UnionEq (g⁻¹ • s) := by sorry
