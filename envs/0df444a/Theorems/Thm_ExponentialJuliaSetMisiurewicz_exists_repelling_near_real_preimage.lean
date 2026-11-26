-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_repelling_near_real_preimage
-- name    : ExponentialJuliaSetMisiurewicz.exists_repelling_near_real_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:08.365373+00:00
-- url     : https://prove2.me/theorems/1a08038c-a498-4acc-93d2-138c11af1eac
-- title:
--   Exponential Julia Set Misiurewicz: exists repelling near real preimage
-- statement:
--   A point mapping to a far right real point is approximated by repelling periodic points.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L317-L400
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L317-L400

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

theorem ExponentialJuliaSetMisiurewicz.exists_repelling_near_real_preimage {a : ℂ} (ha : a ≠ 0)
    {m : ℕ} (hm : expIterate m a = 10) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ ball a ε, ∃ N : ℕ,
      0 < N ∧ expIterate N p = p ∧ 1 < ‖deriv (expIterate N) p‖ := by sorry
