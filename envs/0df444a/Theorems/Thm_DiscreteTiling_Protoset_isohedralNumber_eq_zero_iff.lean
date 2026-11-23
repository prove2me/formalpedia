-- Prove2me | Theorems.Thm_DiscreteTiling_Protoset_isohedralNumber_eq_zero_iff
-- name    : DiscreteTiling.Protoset.isohedralNumber_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:07:03.649557+00:00
-- url     : https://prove2.me/theorems/4abc979d-0c06-49ff-8d21-06c4d215c89b
-- title:
--   Protoset: isohedral Number eq zero iff
-- statement:
--   The Protoset construction uses the isohedral Number eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L377-L388
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L377-L388

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

theorem DiscreteTiling.Protoset.isohedralNumber_eq_zero_iff {p : TileSetFunction ps Prop H} :
    isohedralNumber ιₜ p = 0 ↔ IsEmpty ιₜ ∨ ∀ t : TileSet ps ιₜ, ¬ p t := by sorry
