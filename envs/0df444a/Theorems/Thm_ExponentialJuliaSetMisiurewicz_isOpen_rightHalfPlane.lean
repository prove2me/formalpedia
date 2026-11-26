-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_isOpen_rightHalfPlane
-- name    : ExponentialJuliaSetMisiurewicz.isOpen_rightHalfPlane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:06.006345+00:00
-- url     : https://prove2.me/theorems/23ffe3fa-2a4a-5325-944e-987348f30696
-- title:
--   Exponential Julia Set Misiurewicz: is Open right Half Plane
-- statement:
--   The half-plane `Re z > 4` is open.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L330-L331
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L330-L331

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

theorem ExponentialJuliaSetMisiurewicz.isOpen_rightHalfPlane : IsOpen rightHalfPlane := by sorry
