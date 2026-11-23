-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_StronglyPeriodic_index_ne_zero_of_free
-- name    : DiscreteTiling.TileSet.StronglyPeriodic.index_ne_zero_of_free
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:08:28.47765+00:00
-- url     : https://prove2.me/theorems/c35ba6fe-2254-46ba-9e59-5ae46b1ad7f5
-- title:
--   Strongly Periodic: index ne zero of free
-- statement:
--   The Strongly Periodic construction uses the index ne zero of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L115-L147
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L115-L147

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Nat Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.StronglyPeriodic.index_ne_zero_of_free [Nonempty X] {t : TileSet ps ιₜ}
    (h : t.StronglyPeriodic) {H : Subgroup G} [IsCancelSMul H X] (hi : H.index ≠ 0) :
    t.symmetryGroup.index ≠ 0 := by sorry
