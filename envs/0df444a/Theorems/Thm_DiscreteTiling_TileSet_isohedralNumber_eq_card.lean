-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_eq_card
-- name    : DiscreteTiling.TileSet.isohedralNumber_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:04:23.437042+00:00
-- url     : https://prove2.me/theorems/173be215-cc81-413e-b20a-a15409979466
-- title:
--   Tile Set: isohedral Number eq card
-- statement:
--   The Tile Set construction uses the isohedral Number eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L155-L157
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L155-L157

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

theorem DiscreteTiling.TileSet.isohedralNumber_eq_card (t : TileSet ps ιₜ) :
    t.isohedralNumber = #(MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by sorry
