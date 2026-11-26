-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_unit_ball_subset_iterate_real
-- name    : ExponentialJuliaSetMisiurewicz.eventually_unit_ball_subset_iterate_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:12.659173+00:00
-- url     : https://prove2.me/theorems/985cf17d-9210-5671-b20e-c4669f6d35e5
-- title:
--   Exponential Julia Set Misiurewicz: eventually unit ball subset iterate real
-- statement:
--   Iterated images of a disk on a sufficiently far right real orbit contain unit disks.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L67-L103
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L67-L103

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

theorem ExponentialJuliaSetMisiurewicz.eventually_unit_ball_subset_iterate_real {x : ℂ} (hx : x.im = 0)
    (hx2 : 2 ≤ x.re) {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ n ≥ N, ball (expIterate n x) 1 ⊆ expIterate n '' ball x r := by sorry
