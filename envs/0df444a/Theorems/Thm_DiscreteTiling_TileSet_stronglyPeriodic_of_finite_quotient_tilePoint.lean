-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_of_finite_quotient_tilePoint
-- name    : DiscreteTiling.TileSet.stronglyPeriodic_of_finite_quotient_tilePoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:08:45.733287+00:00
-- url     : https://prove2.me/theorems/22a2eeb6-6520-421a-90b4-617df4363021
-- title:
--   Tile Set: strongly Periodic of finite quotient tile Point
-- statement:
--   The Tile Set construction uses the strongly Periodic of finite quotient tile Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L163-L170
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L163-L170

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

theorem DiscreteTiling.TileSet.stronglyPeriodic_of_finite_quotient_tilePoint {t : TileSet ps ιₜ}
    (hf : Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}))
    (hu : t.UnionEqUniv) : t.StronglyPeriodic := by sorry
