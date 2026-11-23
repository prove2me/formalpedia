-- Prove2me | Theorems.Thm_DiscreteTiling_Protoset_le_isohedralNumber_iff
-- name    : DiscreteTiling.Protoset.le_isohedralNumber_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:05:06.008078+00:00
-- url     : https://prove2.me/theorems/3357a425-7797-43af-9ced-f3eafeaa1c3a
-- title:
--   Protoset: le isohedral Number iff
-- statement:
--   The Protoset construction uses the le isohedral Number iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L394-L410
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L394-L410

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

theorem DiscreteTiling.Protoset.le_isohedralNumber_iff {p : TileSetFunction ps Prop H} {c : Cardinal} (h : c ≠ 0) :
    c ≤ isohedralNumber ιₜ p ↔
      (∃ t : TileSet ps ιₜ, p t) ∧ ∀ t : TileSet ps ιₜ, p t → c ≤ t.isohedralNumber := by sorry
