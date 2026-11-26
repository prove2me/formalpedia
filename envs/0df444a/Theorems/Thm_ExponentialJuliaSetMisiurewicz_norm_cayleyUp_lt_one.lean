-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_norm_cayleyUp_lt_one
-- name    : ExponentialJuliaSetMisiurewicz.norm_cayleyUp_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:34.480074+00:00
-- url     : https://prove2.me/theorems/a57b55b5-5b29-46db-b6ad-340355253a96
-- title:
--   Exponential Julia Set Misiurewicz: norm cayley Up lt one
-- statement:
--   `z ↦ (z - i)/(z + i)` maps the upper half-plane into the unit disc.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L119-L129
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L119-L129

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

theorem ExponentialJuliaSetMisiurewicz.norm_cayleyUp_lt_one {z : ℂ} (hz : 0 < z.im) :
    ‖(z - Complex.I) / (z + Complex.I)‖ < 1 := by sorry
