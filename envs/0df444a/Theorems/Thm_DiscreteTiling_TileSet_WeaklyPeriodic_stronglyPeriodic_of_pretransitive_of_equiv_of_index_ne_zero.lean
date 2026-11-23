-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_WeaklyPeriodic_stronglyPeriodic_of_pretransitive_of_equiv_of_index_ne_zero
-- name    : DiscreteTiling.TileSet.WeaklyPeriodic.stronglyPeriodic_of_pretransitive_of_equiv_of_index_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:17:51.939549+00:00
-- url     : https://prove2.me/theorems/29f48d54-0820-484c-bcf7-f65b9d6de733
-- title:
--   Weakly Periodic: strongly Periodic of pretransitive of equiv of index ne zero
-- statement:
--   In a space with a ℤ^n subgroup of finite index, where `G` acts transitively on `X`, a weakly
--   `n`-periodic `TileSet` is strongly periodic.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L308-L313
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L308-L313

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

theorem DiscreteTiling.TileSet.WeaklyPeriodic.stronglyPeriodic_of_pretransitive_of_equiv_of_index_ne_zero {n : ℕ}
    {t : TileSet ps ιₜ} (h : t.WeaklyPeriodic n) [MulAction.IsPretransitive G X] {H : Subgroup G}
    (e : H ≃* (Fin n → Multiplicative ℤ)) (hi : H.index ≠ 0) : t.StronglyPeriodic := by sorry
