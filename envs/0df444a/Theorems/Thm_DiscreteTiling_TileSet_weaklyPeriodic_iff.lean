-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_weaklyPeriodic_iff
-- name    : DiscreteTiling.TileSet.weaklyPeriodic_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:08:45.492365+00:00
-- url     : https://prove2.me/theorems/04c31034-ea3b-4973-9f98-b0522aae0eab
-- title:
--   Tile Set: weakly Periodic iff
-- statement:
--   The Tile Set construction uses the weakly Periodic iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L215-L217
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L215-L217

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

theorem DiscreteTiling.TileSet.weaklyPeriodic_iff {n : ℕ} {t : TileSet ps ιₜ} :
    t.WeaklyPeriodic n ↔ ∃ f : (Fin n → Multiplicative ℤ) →* t.symmetryGroup, Injective f := by sorry
