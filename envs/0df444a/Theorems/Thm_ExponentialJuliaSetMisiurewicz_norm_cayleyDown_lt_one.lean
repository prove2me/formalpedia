-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_norm_cayleyDown_lt_one
-- name    : ExponentialJuliaSetMisiurewicz.norm_cayleyDown_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:04.171674+00:00
-- url     : https://prove2.me/theorems/5018cc30-e6a5-4a68-a025-b0d73fc1faf2
-- title:
--   Exponential Julia Set Misiurewicz: norm cayley Down lt one
-- statement:
--   `z ↦ (z + i)/(z - i)` maps the lower half-plane into the unit disc.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L132-L142
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L132-L142

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

theorem ExponentialJuliaSetMisiurewicz.norm_cayleyDown_lt_one {z : ℂ} (hz : z.im < 0) :
    ‖(z + Complex.I) / (z - Complex.I)‖ < 1 := by sorry
