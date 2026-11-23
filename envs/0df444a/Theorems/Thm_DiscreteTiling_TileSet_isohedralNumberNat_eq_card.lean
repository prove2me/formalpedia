-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isohedralNumberNat_eq_card
-- name    : DiscreteTiling.TileSet.isohedralNumberNat_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:10:11.812316+00:00
-- url     : https://prove2.me/theorems/b4b8d5e1-8e35-4ede-ab24-d48e646c9f52
-- title:
--   Tile Set: isohedral Number Nat eq card
-- statement:
--   The Tile Set construction uses the isohedral Number Nat eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L196-L199
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L196-L199

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

theorem DiscreteTiling.TileSet.isohedralNumberNat_eq_card (t : TileSet ps ιₜ) :
    t.isohedralNumberNat =
      Nat.card (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by sorry
