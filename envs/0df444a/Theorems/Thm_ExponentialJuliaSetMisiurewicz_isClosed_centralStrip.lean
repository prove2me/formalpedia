-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_isClosed_centralStrip
-- name    : ExponentialJuliaSetMisiurewicz.isClosed_centralStrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:03.601717+00:00
-- url     : https://prove2.me/theorems/47b00a6c-343d-5845-81ba-63273bd56b32
-- title:
--   Exponential Julia Set Misiurewicz: is Closed central Strip
-- statement:
--   The central strip is closed, since the absolute imaginary-part function is continuous.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L326-L327
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L326-L327

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.isClosed_centralStrip : IsClosed centralStrip := by sorry
