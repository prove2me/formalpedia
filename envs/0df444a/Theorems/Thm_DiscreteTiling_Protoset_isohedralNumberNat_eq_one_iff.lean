-- Prove2me | Theorems.Thm_DiscreteTiling_Protoset_isohedralNumberNat_eq_one_iff
-- name    : DiscreteTiling.Protoset.isohedralNumberNat_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:10:46.398923+00:00
-- url     : https://prove2.me/theorems/edea6f1a-822d-44af-bd29-d0b69b7757a6
-- title:
--   Protoset: isohedral Number Nat eq one iff
-- statement:
--   The Protoset construction uses the isohedral Number Nat eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L443-L447
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L443-L447

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
open DiscreteTiling.Protoset
variable {H : Subgroup G}

theorem DiscreteTiling.Protoset.isohedralNumberNat_eq_one_iff {p : TileSetFunction ps Prop H} :
    isohedralNumberNat ιₜ p = 1 ↔ Nonempty ιₜ ∧ ∃ t : TileSet ps ιₜ, p t
      ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by sorry
