-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_logIterate_real_ball
-- name    : ExponentialJuliaSetMisiurewicz.logIterate_real_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:49.355201+00:00
-- url     : https://prove2.me/theorems/04e6b3f3-0261-40bf-b4b4-ad476766ee99
-- title:
--   Exponential Julia Set Misiurewicz: log Iterate real ball
-- statement:
--   Principal logarithms pull disks back along a far right real orbit.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L105-L140
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L105-L140

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

theorem ExponentialJuliaSetMisiurewicz.logIterate_real_ball {x : ℂ} (hx : x.im = 0) (hx10 : 10 ≤ x.re) (n : ℕ) :
    logIterate n (expIterate n x) = x ∧
    MapsTo (logIterate n) (ball (expIterate n x) 8) (ball x 8) ∧
    LipschitzOnWith ((1 / 2 : ℝ≥0) ^ n) (logIterate n) (ball (expIterate n x) 8) ∧
    ∀ z ∈ ball (expIterate n x) 8, expIterate n (logIterate n z) = z := by sorry
