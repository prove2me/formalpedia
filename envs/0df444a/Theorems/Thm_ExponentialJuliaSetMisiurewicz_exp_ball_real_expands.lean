-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_exp_ball_real_expands
-- name    : ExponentialJuliaSetMisiurewicz.exp_ball_real_expands
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:30.593321+00:00
-- url     : https://prove2.me/theorems/0cf776ee-dd43-5bbd-a2ad-47bc5905ecb6
-- title:
--   Exponential Julia Set Misiurewicz: exp ball real expands
-- statement:
--   A small disk centred on the real axis is expanded by a prescribed factor.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L38-L64
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L38-L64

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

theorem ExponentialJuliaSetMisiurewicz.exp_ball_real_expands {x : ℂ} (hx : x.im = 0)
    {r m : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hm : 0 ≤ m)
    (hxm : m ≤ x.re) :
    ball (Complex.exp x) (r * m) ⊆ Complex.exp '' ball x r := by sorry
