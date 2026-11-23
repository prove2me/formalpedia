-- Prove2me | Theorems.Thm_DiscreteTiling_Protoset_weaklyAperiodic_of_aleph0_le_isohedralNumber
-- name    : DiscreteTiling.Protoset.weaklyAperiodic_of_aleph0_le_isohedralNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:08:59.434803+00:00
-- url     : https://prove2.me/theorems/4048ccbb-94c0-4193-bbcd-2790cc5c2747
-- title:
--   Protoset: weakly Aperiodic of aleph0 le isohedral Number
-- statement:
--   The Protoset construction uses the weakly Aperiodic of aleph0 le isohedral Number property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L368-L379
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L368-L379

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
open DiscreteTiling.Protoset
variable {H : Subgroup G}

theorem DiscreteTiling.Protoset.weaklyAperiodic_of_aleph0_le_isohedralNumber {p : TileSetFunction ps Prop H}
    (h : ℵ₀ ≤ ps.isohedralNumber ιₜ p)
    (hf : ∀ t : TileSet ps ιₜ, p t → t.FiniteDistinctIntersections)
    (hn : ∀ i, (ps i : Set X).Nonempty) : ps.WeaklyAperiodic ιₜ p := by sorry
