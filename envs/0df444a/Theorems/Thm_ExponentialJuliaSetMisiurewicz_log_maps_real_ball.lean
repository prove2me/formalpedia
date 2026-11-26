-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_log_maps_real_ball
-- name    : ExponentialJuliaSetMisiurewicz.log_maps_real_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:32.097383+00:00
-- url     : https://prove2.me/theorems/f865651d-501f-4c42-898a-d1f760953d6b
-- title:
--   Exponential Julia Set Misiurewicz: log maps real ball
-- statement:
--   The principal logarithm sends the radius-eight disk about `exp x` into the
--   radius-eight disk about `x`, for real `x ≥ 10`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L91-L102
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L91-L102

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

theorem ExponentialJuliaSetMisiurewicz.log_maps_real_ball {x : ℂ} (hx : x.im = 0) (hx10 : 10 ≤ x.re) :
    MapsTo Complex.log (ball (Complex.exp x) 8) (ball x 8) := by sorry
