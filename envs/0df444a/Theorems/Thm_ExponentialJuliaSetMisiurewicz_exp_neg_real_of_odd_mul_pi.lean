-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_exp_neg_real_of_odd_mul_pi
-- name    : ExponentialJuliaSetMisiurewicz.exp_neg_real_of_odd_mul_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:56.627707+00:00
-- url     : https://prove2.me/theorems/3ea86825-849b-4757-a7f6-f74bf5eedf01
-- title:
--   Exponential Julia Set Misiurewicz: exp neg real of odd mul pi
-- statement:
--   An odd multiple of `π` in the imaginary part gives a negative real exponential.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L76-L85
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L76-L85

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

theorem ExponentialJuliaSetMisiurewicz.exp_neg_real_of_odd_mul_pi {z : ℂ} {k : ℤ} (hk : Odd k)
    (h : z.im = (k : ℝ) * Real.pi) :
    (Complex.exp z).im = 0 ∧ (Complex.exp z).re < 0 := by sorry
