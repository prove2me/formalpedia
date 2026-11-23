-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_of_finite_quotient_of_index_ne_zero
-- name    : DiscreteTiling.TileSet.stronglyPeriodic_of_finite_quotient_of_index_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:08:29.658094+00:00
-- url     : https://prove2.me/theorems/bfe3edea-0432-4451-b3fd-1a6c60b9900f
-- title:
--   Tile Set: strongly Periodic of finite quotient of index ne zero
-- statement:
--   The Tile Set construction uses the strongly Periodic of finite quotient of index ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L91-L94
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L91-L94

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

theorem DiscreteTiling.TileSet.stronglyPeriodic_of_finite_quotient_of_index_ne_zero {t : TileSet ps ιₜ}
    [Finite <| MulAction.orbitRel.Quotient G X] (hi : t.symmetryGroup.index ≠ 0) :
    t.StronglyPeriodic := by sorry
