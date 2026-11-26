-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_mem_exp_exp_ball_real
-- name    : ExponentialJuliaSetMisiurewicz.mem_exp_exp_ball_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:32.72163+00:00
-- url     : https://prove2.me/theorems/5283b317-dbe4-47a3-86b7-ba717d262715
-- title:
--   Exponential Julia Set Misiurewicz: mem exp exp ball real
-- statement:
--   Two exponentials of a radius-eight disk sufficiently far along the real axis
--   cover any prescribed annulus. Integer translates of a logarithm supply the preimages.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L107-L163
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L107-L163

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

theorem ExponentialJuliaSetMisiurewicz.mem_exp_exp_ball_real {w : ℂ} (hw : w ≠ 0) {M x : ℝ}
    (hwM : |Real.log ‖w‖| ≤ M) (hx : M + 2 * Real.pi ≤ x) :
    w ∈ expIterate 2 '' ball (x : ℂ) 8 := by sorry
