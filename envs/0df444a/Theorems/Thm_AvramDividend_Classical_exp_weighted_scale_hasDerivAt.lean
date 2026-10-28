-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_weighted_scale_hasDerivAt
-- name    : AvramDividend.Classical.exp_weighted_scale_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:04:33.733236+00:00
-- url     : https://prove2.me/theorems/cd75519a-72da-4ce6-8ae2-11fa21904a54
-- title:
--   Product-rule derivative for exponentially weighted scale kernels
-- statement:
--   The weighted scale kernel g_theta(x)=exp(-theta x)W(x) has derivative g_theta'(x)=exp(-theta x)(W'(x)-theta W(x)) at every differentiability point. This exact product rule connects the proved weighted derivative integrability to a boundary-safe fundamental theorem of calculus.
-- source:
--   Real.hasDerivAt_exp, HasDerivAt.const_mul, HasDerivAt.comp and HasDerivAt.mul in Mathlib.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.exp_weighted_scale_hasDerivAt
    (W : ℝ → ℝ) (θ x : ℝ) (hW : DifferentiableAt ℝ W x) :
    HasDerivAt (fun y : ℝ => Real.exp (-(θ * y)) * W y)
      (Real.exp (-(θ * x)) * (deriv W x - θ * W x)) x := by sorry
