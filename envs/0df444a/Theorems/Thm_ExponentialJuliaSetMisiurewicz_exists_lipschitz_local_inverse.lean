-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_lipschitz_local_inverse
-- name    : ExponentialJuliaSetMisiurewicz.exists_lipschitz_local_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:19.353775+00:00
-- url     : https://prove2.me/theorems/2911aa87-cf7c-49a9-bc85-b1bfbaaf5616
-- title:
--   Exponential Julia Set Misiurewicz: exists lipschitz local inverse
-- statement:
--   A noncritical holomorphic map has a Lipschitz inverse on a small image disk.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L50-L63
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L50-L63

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

theorem ExponentialJuliaSetMisiurewicz.exists_lipschitz_local_inverse {f : ℂ → ℂ} {a : ℂ}
    (hf : HasStrictDerivAt f (deriv f a) a) (hne : deriv f a ≠ 0) :
    ∃ g : ℂ → ℂ, ∃ C : ℝ≥0, ∃ s : ℝ, 0 < s ∧
      g (f a) = a ∧ LipschitzOnWith C g (ball (f a) s) ∧
      ∀ z ∈ ball (f a) s, f (g z) = z := by sorry
