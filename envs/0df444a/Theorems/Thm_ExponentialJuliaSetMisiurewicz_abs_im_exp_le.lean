-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_abs_im_exp_le
-- name    : ExponentialJuliaSetMisiurewicz.abs_im_exp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:33.470776+00:00
-- url     : https://prove2.me/theorems/a9504a8a-953c-40eb-83e3-4f562f293a93
-- title:
--   Exponential Julia Set Misiurewicz: abs im exp le
-- statement:
--   The imaginary part of an exponential is controlled by the imaginary
--   part of its argument and the norm of the exponential.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L56-L63
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L56-L63

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

theorem ExponentialJuliaSetMisiurewicz.abs_im_exp_le (w : ℂ) :
    |(Complex.exp w).im| ≤
      |w.im| * ‖Complex.exp w‖ := by sorry
