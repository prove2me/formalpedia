-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_StronglyPeriodic_isohedralNumber_lt_aleph0
-- name    : DiscreteTiling.TileSet.StronglyPeriodic.isohedralNumber_lt_aleph0
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:08:28.572593+00:00
-- url     : https://prove2.me/theorems/265f6c16-a631-49ab-b86d-24c982ea2121
-- title:
--   Strongly Periodic: isohedral Number lt aleph0
-- statement:
--   The Strongly Periodic construction uses the isohedral Number lt aleph0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L177-L181
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L177-L181

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

theorem DiscreteTiling.TileSet.StronglyPeriodic.isohedralNumber_lt_aleph0 {t : TileSet ps ιₜ} (h : t.StronglyPeriodic)
    (hf : t.FiniteDistinctIntersections) (hn : ∀ i, (t i : Set X).Nonempty) :
    t.isohedralNumber < ℵ₀ := by sorry
