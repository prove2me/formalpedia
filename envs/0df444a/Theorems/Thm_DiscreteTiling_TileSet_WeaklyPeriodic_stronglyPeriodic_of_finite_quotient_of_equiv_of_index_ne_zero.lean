-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_WeaklyPeriodic_stronglyPeriodic_of_finite_quotient_of_equiv_of_index_ne_zero
-- name    : DiscreteTiling.TileSet.WeaklyPeriodic.stronglyPeriodic_of_finite_quotient_of_equiv_of_index_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:08:56.742751+00:00
-- url     : https://prove2.me/theorems/5925b1b0-3934-48a1-9e2a-2db84647d38d
-- title:
--   Weakly Periodic: strongly Periodic of finite quotient of equiv of index ne zero
-- statement:
--   In a space with a ℤ^n subgroup of finite index, where `X` has finite quotient by the action
--   of `G`, a weakly `n`-periodic `TileSet` is strongly periodic.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L281-L304
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L281-L304

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

theorem DiscreteTiling.TileSet.WeaklyPeriodic.stronglyPeriodic_of_finite_quotient_of_equiv_of_index_ne_zero {n : ℕ}
    {t : TileSet ps ιₜ} (h : t.WeaklyPeriodic n) [Finite <| MulAction.orbitRel.Quotient G X]
    {H : Subgroup G} (e : H ≃* (Fin n → Multiplicative ℤ)) (hi : H.index ≠ 0) :
    t.StronglyPeriodic := by sorry
