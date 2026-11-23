-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_unionEqUniv_reindex_iff_of_surjective
-- name    : DiscreteTiling.TileSet.unionEqUniv_reindex_iff_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:03.725525+00:00
-- url     : https://prove2.me/theorems/e92ad51f-a3d8-4cf4-8343-24ddd8d846ba
-- title:
--   Tile Set: union Eq Univ reindex iff of surjective
-- statement:
--   The Tile Set construction uses the union Eq Univ reindex iff of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L116-L118
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L116-L118

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

theorem DiscreteTiling.TileSet.unionEqUniv_reindex_iff_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (h : Surjective e) : (t.reindex e).UnionEqUniv ↔ t.UnionEqUniv := by sorry
