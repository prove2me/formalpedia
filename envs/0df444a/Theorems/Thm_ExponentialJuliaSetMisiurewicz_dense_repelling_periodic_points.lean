-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_repelling_periodic_points
-- name    : ExponentialJuliaSetMisiurewicz.dense_repelling_periodic_points
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:04.21033+00:00
-- url     : https://prove2.me/theorems/a86e8017-0e85-42f0-b638-bf7ca33693f4
-- title:
--   Exponential Julia Set Misiurewicz: dense repelling periodic points
-- statement:
--   Repelling periodic points of the exponential are dense in the complex plane.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L431-L437
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L431-L437

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

theorem ExponentialJuliaSetMisiurewicz.dense_repelling_periodic_points :
    Dense {p : ℂ | ∃ n : ℕ,
      0 < n ∧ expIterate n p = p ∧ 1 < ‖deriv (expIterate n) p‖} := by sorry
