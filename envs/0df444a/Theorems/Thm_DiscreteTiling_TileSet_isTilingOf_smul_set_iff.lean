-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isTilingOf_smul_set_iff
-- name    : DiscreteTiling.TileSet.isTilingOf_smul_set_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:09:26.202135+00:00
-- url     : https://prove2.me/theorems/a4de9702-b12d-45b9-9e2b-8d3b6303932a
-- title:
--   Tile Set: is Tiling Of smul set iff
-- statement:
--   The Tile Set construction uses the is Tiling Of smul set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L68-L72
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L68-L72

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

theorem DiscreteTiling.TileSet.isTilingOf_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    t.IsTilingOf (g • s) ↔ (g⁻¹ • t).IsTilingOf s := by sorry
