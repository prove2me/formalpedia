-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_of_isohedralNumber_lt_aleph0
-- name    : DiscreteTiling.TileSet.stronglyPeriodic_of_isohedralNumber_lt_aleph0
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:08:09.317036+00:00
-- url     : https://prove2.me/theorems/d71552ac-150b-47d8-be06-1c4732d855d4
-- title:
--   Tile Set: strongly Periodic of isohedral Number lt aleph0
-- statement:
--   The Tile Set construction uses the strongly Periodic of isohedral Number lt aleph0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L172-L175
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L172-L175

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

theorem DiscreteTiling.TileSet.stronglyPeriodic_of_isohedralNumber_lt_aleph0 {t : TileSet ps ιₜ} (h : t.isohedralNumber < ℵ₀)
    (hf : ∀ i, (t i : Set X).Finite) (hu : t.UnionEqUniv) : t.StronglyPeriodic := by sorry
