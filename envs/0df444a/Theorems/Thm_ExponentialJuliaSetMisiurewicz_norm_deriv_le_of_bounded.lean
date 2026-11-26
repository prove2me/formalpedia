-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_norm_deriv_le_of_bounded
-- name    : ExponentialJuliaSetMisiurewicz.norm_deriv_le_of_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:22.627223+00:00
-- url     : https://prove2.me/theorems/07f06501-3421-59dc-8bb2-8280a03f815d
-- title:
--   Exponential Julia Set Misiurewicz: norm deriv le of bounded
-- statement:
--   Cauchy's estimate: a holomorphic function bounded by `M` has `‖deriv f z‖ ≤ M / r`
--   whenever `closedBall z r` lies in the domain.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L40-L48
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L40-L48

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.norm_deriv_le_of_bounded
    {f : ℂ → ℂ} {U : Set ℂ} {M r : ℝ} {z : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hzr : closedBall z r ⊆ U)
    (hb : ∀ w ∈ U, ‖f w‖ ≤ M) :
    ‖deriv f z‖ ≤ M / r := by sorry
