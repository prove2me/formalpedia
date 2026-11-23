-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_eq_one_iff
-- name    : DiscreteTiling.TileSet.isohedralNumber_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:04:50.991817+00:00
-- url     : https://prove2.me/theorems/a629607a-6672-4a6b-b54f-d94d541aea1b
-- title:
--   Tile Set: isohedral Number eq one iff
-- statement:
--   The Tile Set construction uses the isohedral Number eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L173-L180
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L173-L180

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

theorem DiscreteTiling.TileSet.isohedralNumber_eq_one_iff {t : TileSet ps ιₜ} :
    t.isohedralNumber = 1
      ↔ Nonempty ιₜ ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by sorry
