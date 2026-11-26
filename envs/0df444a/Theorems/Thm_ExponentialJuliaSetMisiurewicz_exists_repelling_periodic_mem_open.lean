-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_repelling_periodic_mem_open
-- name    : ExponentialJuliaSetMisiurewicz.exists_repelling_periodic_mem_open
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:51.597467+00:00
-- url     : https://prove2.me/theorems/44674ba3-cd97-5550-a6d3-2c374ca0eb88
-- title:
--   Exponential Julia Set Misiurewicz: exists repelling periodic mem open
-- statement:
--   **Theorem 6.1.** Every nonempty open set contains a repelling periodic point.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L416-L428
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L416-L428

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Periodic
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.exists_repelling_periodic_mem_open {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ p ∈ U, ∃ n : ℕ,
      0 < n ∧ expIterate n p = p ∧ 1 < ‖deriv (expIterate n) p‖ := by sorry
