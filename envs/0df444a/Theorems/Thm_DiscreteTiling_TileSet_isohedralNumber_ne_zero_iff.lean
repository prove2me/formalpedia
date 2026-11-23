-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_ne_zero_iff
-- name    : DiscreteTiling.TileSet.isohedralNumber_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:04:34.332074+00:00
-- url     : https://prove2.me/theorems/cd8d4ba0-64ef-49e1-bb22-c6e72d41f30c
-- title:
--   Tile Set: isohedral Number ne zero iff
-- statement:
--   The Tile Set construction uses the isohedral Number ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L165-L167
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L165-L167

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.isohedralNumber_ne_zero_iff (t : TileSet ps ιₜ) : t.isohedralNumber ≠ 0 ↔ Nonempty ιₜ := by sorry
