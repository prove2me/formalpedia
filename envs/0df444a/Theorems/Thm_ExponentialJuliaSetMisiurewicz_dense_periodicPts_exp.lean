-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_periodicPts_exp
-- name    : ExponentialJuliaSetMisiurewicz.dense_periodicPts_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:05.708237+00:00
-- url     : https://prove2.me/theorems/feeeb5d0-c2a2-49f0-a2a2-1f72eb6b4185
-- title:
--   Exponential Julia Set Misiurewicz: dense periodic Pts exp
-- statement:
--   The periodic-point benchmark using mathlib's standard `periodicPts` set.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L447-L450
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L447-L450

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

theorem ExponentialJuliaSetMisiurewicz.dense_periodicPts_exp : Dense (Function.periodicPts Complex.exp) := by sorry
