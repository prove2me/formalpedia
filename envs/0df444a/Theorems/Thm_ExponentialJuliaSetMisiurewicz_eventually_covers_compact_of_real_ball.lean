-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_covers_compact_of_real_ball
-- name    : ExponentialJuliaSetMisiurewicz.eventually_covers_compact_of_real_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:35.313846+00:00
-- url     : https://prove2.me/theorems/a00f1e28-8d99-4408-b1ae-387a76e16804
-- title:
--   Exponential Julia Set Misiurewicz: eventually covers compact of real ball
-- statement:
--   Every sufficiently late image of a disk centred on a far right real point
--   covers a given compact subset of the punctured plane.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L180-L223
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L180-L223

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

theorem ExponentialJuliaSetMisiurewicz.eventually_covers_compact_of_real_ball {K : Set ℂ}
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K)
    {x : ℂ} (hx : x.im = 0) (hx2 : 2 ≤ x.re) {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ n ≥ N, K ⊆ expIterate n '' ball x r := by sorry
