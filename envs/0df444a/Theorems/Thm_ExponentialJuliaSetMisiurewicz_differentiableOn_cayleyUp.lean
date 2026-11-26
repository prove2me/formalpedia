-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiableOn_cayleyUp
-- name    : ExponentialJuliaSetMisiurewicz.differentiableOn_cayleyUp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:37.130269+00:00
-- url     : https://prove2.me/theorems/bb706df1-49b0-5a50-80ec-ec9ae2380d17
-- title:
--   Exponential Julia Set Misiurewicz: differentiable On cayley Up
-- statement:
--   The Cayley transform of an iterate is holomorphic wherever the iterate has positive
--   imaginary part.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L214-L221
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L214-L221

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

theorem ExponentialJuliaSetMisiurewicz.differentiableOn_cayleyUp {U : Set ℂ} {n : ℕ}
    (hpos : ∀ z ∈ U, 0 < (expIterate n z).im) :
    DifferentiableOn ℂ
      (fun w => (expIterate n w - Complex.I) / (expIterate n w + Complex.I)) U := by sorry
