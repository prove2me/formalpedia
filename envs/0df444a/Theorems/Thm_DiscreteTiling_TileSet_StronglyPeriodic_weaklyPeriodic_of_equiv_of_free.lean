-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_StronglyPeriodic_weaklyPeriodic_of_equiv_of_free
-- name    : DiscreteTiling.TileSet.StronglyPeriodic.weaklyPeriodic_of_equiv_of_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:17:53.995925+00:00
-- url     : https://prove2.me/theorems/686d2050-714c-406f-ac76-b2e61076bd36
-- title:
--   Strongly Periodic: weakly Periodic of equiv of free
-- statement:
--   In a space with a ℤ^n subgroup of finite index acting freely, a strongly periodic `TileSet`
--   is weakly `n`-periodic.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L317-L337
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L317-L337

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

theorem DiscreteTiling.TileSet.StronglyPeriodic.weaklyPeriodic_of_equiv_of_free [Nonempty X] {n : ℕ} {t : TileSet ps ιₜ}
    (h : t.StronglyPeriodic) {H : Subgroup G} (e : H ≃* (Fin n → Multiplicative ℤ))
    [IsCancelSMul H X] (hi : H.index ≠ 0) : t.WeaklyPeriodic n := by sorry
