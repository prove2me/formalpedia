-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_disjoint_frontier_centralStrip_pi
-- name    : ExponentialJuliaSetMisiurewicz.disjoint_frontier_centralStrip_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:20.570389+00:00
-- url     : https://prove2.me/theorems/a35412c9-7b85-4f4e-9a91-03a9342196fe
-- title:
--   Exponential Julia Set Misiurewicz: disjoint frontier central Strip pi
-- statement:
--   The frontier estimate still bites with `π` in place of `2π`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L586-L593
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L586-L593

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

theorem ExponentialJuliaSetMisiurewicz.disjoint_frontier_centralStrip_pi :
    Disjoint (frontier centralStrip) (piDoubleStrip ∩ rightHalfPlane) := by sorry
