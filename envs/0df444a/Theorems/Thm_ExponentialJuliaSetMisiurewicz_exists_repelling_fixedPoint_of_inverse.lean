-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_repelling_fixedPoint_of_inverse
-- name    : ExponentialJuliaSetMisiurewicz.exists_repelling_fixedPoint_of_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:38.3256+00:00
-- url     : https://prove2.me/theorems/659837a8-c99f-5a1d-9032-4b0af6e2fac4
-- title:
--   Exponential Julia Set Misiurewicz: exists repelling fixed Point of inverse
-- statement:
--   A strictly contracting inverse branch produces a repelling fixed point.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L244-L283
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L244-L283

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

theorem ExponentialJuliaSetMisiurewicz.exists_repelling_fixedPoint_of_inverse
    {f h : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hlip : LipschitzOnWith (1 / 2) h (closedBall a r))
    (hmaps : MapsTo h (closedBall a r) (ball a (r / 2)))
    (hinv : ∀ z ∈ closedBall a r, f (h z) = z)
    (hf : Differentiable ℂ f) (hf0 : ∀ z, deriv f z ≠ 0) :
    ∃ p ∈ ball a r, f p = p ∧ 1 < ‖deriv f p‖ := by sorry
