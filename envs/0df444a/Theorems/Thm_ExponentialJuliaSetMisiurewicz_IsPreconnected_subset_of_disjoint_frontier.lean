-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_IsPreconnected_subset_of_disjoint_frontier
-- name    : ExponentialJuliaSetMisiurewicz.IsPreconnected.subset_of_disjoint_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:10.481136+00:00
-- url     : https://prove2.me/theorems/8b591c3c-ad66-570d-92e7-3f22918a5741
-- title:
--   Is Preconnected: subset of disjoint frontier
-- statement:
--   A connected set disjoint from the frontier of an open set, and meeting it, lies inside it.
--   This is the Lean form of HOL Light's `CONNECTED_INTER_FRONTIER`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L432-L444
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L432-L444

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.IsPreconnected.subset_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hv : IsPreconnected v) (hu : IsOpen u)
    (hdisj : Disjoint (frontier u) v) (hne : (v ∩ u).Nonempty) :
    v ⊆ u := by sorry
