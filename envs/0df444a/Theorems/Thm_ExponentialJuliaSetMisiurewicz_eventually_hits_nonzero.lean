-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_hits_nonzero
-- name    : ExponentialJuliaSetMisiurewicz.eventually_hits_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:22.220839+00:00
-- url     : https://prove2.me/theorems/3b38d917-643c-534b-a510-237227ee4ab1
-- title:
--   Exponential Julia Set Misiurewicz: eventually hits nonzero
-- statement:
--   Every nonzero point belongs to every sufficiently late image of an open set.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L265-L270
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L265-L270

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.eventually_hits_nonzero {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {w : ℂ} (hw : w ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z ∈ U, expIterate n z = w := by sorry
