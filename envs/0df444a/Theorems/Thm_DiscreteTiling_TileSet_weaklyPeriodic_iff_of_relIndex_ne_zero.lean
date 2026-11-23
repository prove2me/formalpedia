-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_weaklyPeriodic_iff_of_relIndex_ne_zero
-- name    : DiscreteTiling.TileSet.weaklyPeriodic_iff_of_relIndex_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:08:52.148269+00:00
-- url     : https://prove2.me/theorems/d1119bfa-cea4-4a0a-9ceb-dd51d488337d
-- title:
--   Tile Set: weakly Periodic iff of rel Index ne zero
-- statement:
--   The Tile Set construction uses the weakly Periodic iff of rel Index ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L247-L271
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L247-L271

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

theorem DiscreteTiling.TileSet.weaklyPeriodic_iff_of_relIndex_ne_zero {n : ℕ} {t : TileSet ps ιₜ} {H : Subgroup G}
    (hi : H.relIndex t.symmetryGroup ≠ 0) :
    t.WeaklyPeriodic n ↔
      ∃ f : (Fin n → Multiplicative ℤ) →* (H ⊓ t.symmetryGroup : Subgroup G), Injective f := by sorry
