-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_abs_im_le_norm_aux
-- name    : ExponentialJuliaSetMisiurewicz.abs_im_le_norm_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:43.830963+00:00
-- url     : https://prove2.me/theorems/c3aa4e59-232b-57ed-b653-1e711a5afc3a
-- title:
--   Exponential Julia Set Misiurewicz: abs im le norm aux
-- statement:
--   The absolute value of the imaginary part is at most the complex norm.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L66-L68
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L66-L68

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.abs_im_le_norm_aux (w : ℂ) :
    |w.im| ≤ ‖w‖ := by sorry
