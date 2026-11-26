-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_abs_im_exp_gt_two_pi_of_frontier
-- name    : ExponentialJuliaSetMisiurewicz.abs_im_exp_gt_two_pi_of_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:05.824446+00:00
-- url     : https://prove2.me/theorems/3b02f44a-b21a-5882-a365-313d85c42927
-- title:
--   Exponential Julia Set Misiurewicz: abs im exp gt two pi of frontier
-- statement:
--   **The geometric heart of Lemma 5.** On the frontier of the central strip, inside the
--   right half-plane, the exponential throws points clear of the wide strip: `|sin| = √3/2`
--   there, and `e^4 · √3/2` already exceeds `2π`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L401-L428
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L401-L428

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

theorem ExponentialJuliaSetMisiurewicz.abs_im_exp_gt_two_pi_of_frontier
    {z : ℂ} (hfr : |z.im| = Real.pi / 3) (hre : 4 < z.re) :
    2 * Real.pi < |(Complex.exp z).im| := by sorry
