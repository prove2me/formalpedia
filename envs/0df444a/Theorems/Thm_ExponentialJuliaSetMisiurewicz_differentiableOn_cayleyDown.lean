-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiableOn_cayleyDown
-- name    : ExponentialJuliaSetMisiurewicz.differentiableOn_cayleyDown
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:06.93516+00:00
-- url     : https://prove2.me/theorems/e86003f9-9378-408f-8cfb-9ebd79b0661a
-- title:
--   Exponential Julia Set Misiurewicz: differentiable On cayley Down
-- statement:
--   The lower-half-plane Cayley transform of an iterate is holomorphic wherever
--   that iterate has negative imaginary part.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L225-L232
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L225-L232

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

theorem ExponentialJuliaSetMisiurewicz.differentiableOn_cayleyDown {U : Set ℂ} {n : ℕ}
    (hneg : ∀ z ∈ U, (expIterate n z).im < 0) :
    DifferentiableOn ℂ
      (fun w => (expIterate n w + Complex.I) / (expIterate n w - Complex.I)) U := by sorry
