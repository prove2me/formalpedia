-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_lt_aleph0_iff
-- name    : DiscreteTiling.TileSet.isohedralNumber_lt_aleph0_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:04:46.402679+00:00
-- url     : https://prove2.me/theorems/06115c2b-96c5-4856-ad0c-ed9cf3bb0e4e
-- title:
--   Tile Set: isohedral Number lt aleph0 iff
-- statement:
--   The Tile Set construction uses the isohedral Number lt aleph0 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L187-L190
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L187-L190

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

theorem DiscreteTiling.TileSet.isohedralNumber_lt_aleph0_iff {t : TileSet ps ιₜ} :
    t.isohedralNumber < ℵ₀ ↔
      Finite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by sorry
