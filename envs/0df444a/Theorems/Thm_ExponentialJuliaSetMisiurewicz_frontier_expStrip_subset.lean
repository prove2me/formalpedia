-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_frontier_expStrip_subset
-- name    : ExponentialJuliaSetMisiurewicz.frontier_expStrip_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:23.782474+00:00
-- url     : https://prove2.me/theorems/7ede4b68-76e8-55e8-8363-ef172b09bbf2
-- title:
--   Exponential Julia Set Misiurewicz: frontier exp Strip subset
-- statement:
--   On the frontier of the preimage of the wide strip, `|Im (exp z)| = 2π`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L491-L495
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L491-L495

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

theorem ExponentialJuliaSetMisiurewicz.frontier_expStrip_subset :
    frontier {z : ℂ | |(Complex.exp z).im| ≤ 2 * Real.pi}
      ⊆ {z : ℂ | |(Complex.exp z).im| = 2 * Real.pi} := by sorry
