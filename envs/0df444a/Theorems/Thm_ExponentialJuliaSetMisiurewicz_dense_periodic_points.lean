-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_periodic_points
-- name    : ExponentialJuliaSetMisiurewicz.dense_periodic_points
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:54.480795+00:00
-- url     : https://prove2.me/theorems/1e1756cf-a0c2-471c-8bc0-8709b87d4682
-- title:
--   Exponential Julia Set Misiurewicz: dense periodic points
-- statement:
--   Periodic points of the exponential are dense in the plane.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L440-L444
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L440-L444

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

theorem ExponentialJuliaSetMisiurewicz.dense_periodic_points :
    Dense {p : ℂ | ∃ n : ℕ, 0 < n ∧ expIterate n p = p} := by sorry
