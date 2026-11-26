-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_covers_compact_ball
-- name    : ExponentialJuliaSetMisiurewicz.eventually_covers_compact_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:59.426113+00:00
-- url     : https://prove2.me/theorems/3155c797-8b18-5281-805b-df1818656684
-- title:
--   Exponential Julia Set Misiurewicz: eventually covers compact ball
-- statement:
--   The compact covering theorem specialised to an open ball of positive radius.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L259-L262
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L259-L262

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

theorem ExponentialJuliaSetMisiurewicz.eventually_covers_compact_ball {c : ℂ} {r : ℝ} (hr : 0 < r)
    {K : Set ℂ} (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ N : ℕ, ∀ n ≥ N, K ⊆ expIterate n '' ball c r := by sorry
