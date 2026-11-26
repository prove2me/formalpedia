-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_disjoint_frontier_centralStrip
-- name    : ExponentialJuliaSetMisiurewicz.disjoint_frontier_centralStrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:32.045962+00:00
-- url     : https://prove2.me/theorems/eacea284-5dee-5792-b186-cb475c2ed970
-- title:
--   Exponential Julia Set Misiurewicz: disjoint frontier central Strip
-- statement:
--   The frontier of the central strip misses `w ∩ h`: this is where the estimate bites.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L498-L503
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L498-L503

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

theorem ExponentialJuliaSetMisiurewicz.disjoint_frontier_centralStrip :
    Disjoint (frontier centralStrip) (doubleStrip ∩ rightHalfPlane) := by sorry
