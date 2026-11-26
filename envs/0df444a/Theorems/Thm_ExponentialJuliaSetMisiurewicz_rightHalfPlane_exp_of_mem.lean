-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_rightHalfPlane_exp_of_mem
-- name    : ExponentialJuliaSetMisiurewicz.rightHalfPlane_exp_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:04.167277+00:00
-- url     : https://prove2.me/theorems/04a9e2e5-c752-5046-b054-2d636989240b
-- title:
--   Exponential Julia Set Misiurewicz: right Half Plane exp of mem
-- statement:
--   Points of the central strip in the right half-plane stay in the right half-plane.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L516-L525
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L516-L525

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.rightHalfPlane_exp_of_mem {z : ℂ}
    (hs : z ∈ centralStrip) (hh : z ∈ rightHalfPlane) :
    Complex.exp z ∈ rightHalfPlane := by sorry
