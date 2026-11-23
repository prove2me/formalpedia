-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isTilingOf_smul_tileSet_iff
-- name    : DiscreteTiling.TileSet.isTilingOf_smul_tileSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:09:32.473043+00:00
-- url     : https://prove2.me/theorems/f6aaa650-8e5f-40bd-a2ac-eabb19025785
-- title:
--   Tile Set: is Tiling Of smul tile Set iff
-- statement:
--   The Tile Set construction uses the is Tiling Of smul tile Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L74-L78
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L74-L78

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

theorem DiscreteTiling.TileSet.isTilingOf_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    (g • t).IsTilingOf s ↔ t.IsTilingOf (g⁻¹ • s) := by sorry
