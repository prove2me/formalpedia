-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isTilingOf_empty
-- name    : DiscreteTiling.TileSet.isTilingOf_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:38.651798+00:00
-- url     : https://prove2.me/theorems/69000389-c4de-477f-a445-a6097302c407
-- title:
--   Tile Set: is Tiling Of empty
-- statement:
--   The Tile Set construction uses the is Tiling Of empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L80-L81
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L80-L81

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

theorem DiscreteTiling.TileSet.isTilingOf_empty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : t.IsTilingOf ∅ := by sorry
