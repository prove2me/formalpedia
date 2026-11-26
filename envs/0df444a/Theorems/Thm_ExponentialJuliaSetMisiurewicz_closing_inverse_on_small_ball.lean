-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_closing_inverse_on_small_ball
-- name    : ExponentialJuliaSetMisiurewicz.closing_inverse_on_small_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:49.139494+00:00
-- url     : https://prove2.me/theorems/1455d95a-581f-481e-b31c-dbafe975feaf
-- title:
--   Exponential Julia Set Misiurewicz: closing inverse on small ball
-- statement:
--   A uniform family of two-step inverse branches on a small closed disk.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L286-L314
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L286-L314

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

theorem ExponentialJuliaSetMisiurewicz.closing_inverse_on_small_ball {a : ℂ} (ha : a ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ ∃ C : ℝ≥0, ∃ ρ : ℝ,
      ∀ x : ℝ, ρ ≤ x → ∃ ψ : ℂ → ℂ,
        LipschitzOnWith C ψ (closedBall a r) ∧
        MapsTo ψ (closedBall a r) (ball (x : ℂ) 8) ∧
        ∀ z ∈ closedBall a r, expIterate 2 (ψ z) = z := by sorry
