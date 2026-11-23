-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_weaklyPeriodic_of_le
-- name    : DiscreteTiling.TileSet.weaklyPeriodic_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:18:03.333838+00:00
-- url     : https://prove2.me/theorems/0157a93e-2b7e-47a1-8088-5c0847737be2
-- title:
--   Tile Set: weakly Periodic of le
-- statement:
--   The Tile Set construction uses the weakly Periodic of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L241-L245
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L241-L245

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

theorem DiscreteTiling.TileSet.weaklyPeriodic_of_le {t : TileSet ps ιₜ} {m n : ℕ} (h : t.WeaklyPeriodic n) (hle : m ≤ n) :
    t.WeaklyPeriodic m := by sorry
