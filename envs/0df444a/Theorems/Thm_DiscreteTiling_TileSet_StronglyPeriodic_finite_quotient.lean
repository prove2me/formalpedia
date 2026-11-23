-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_StronglyPeriodic_finite_quotient
-- name    : DiscreteTiling.TileSet.StronglyPeriodic.finite_quotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:12:37.799108+00:00
-- url     : https://prove2.me/theorems/ae1b2544-9cef-4b2b-9f24-70d91ed98f28
-- title:
--   Strongly Periodic: finite quotient
-- statement:
--   The Strongly Periodic construction uses the finite quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L101-L113
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L101-L113

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

theorem DiscreteTiling.TileSet.StronglyPeriodic.finite_quotient {t : TileSet ps ιₜ} (h : t.StronglyPeriodic) :
    Finite <| MulAction.orbitRel.Quotient G X := by sorry
