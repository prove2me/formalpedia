-- Prove2me | Theorems.Thm_CurveCalculus_second_derivative_along_smooth_curve
-- name    : CurveCalculus.second_derivative_along_smooth_curve
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T18:40:36.260789+00:00
-- url     : https://prove2.me/theorems/5f09c996-126e-4381-bbcd-d585f3fd50a1
-- title:
--   Second derivative along a smooth curve with acceleration
-- statement:
--   For a smooth real-valued function F on an arbitrary real normed vector space and a smooth curve gamma at any real time t0, suppose gamma(t0)=y and its velocity is v. The second derivative of F composed with gamma equals the directional Hessian at y applied twice to v, plus the first derivative of F at y applied to the curve acceleration. Smoothness is assumed locally at t0 and y; no finite-dimensional or completeness assumption is imposed.
-- source:
--   Original auxiliary result generalized from Solutions/Sol_ConvexAnalysis_convex_frontier_radial_derivative_positive.lean:130. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Analysis/Calculus/LocalExtr/Basic.lean; Analysis/Calculus/ContDiff/Deriv.lean; Analysis/Calculus/Deriv/Mul.lean. https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus. No claim of a separate article theorem.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.NormNum
open Set Filter
open scoped Topology ContDiff
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem CurveCalculus.second_derivative_along_smooth_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (γ : ℝ → E)
    (t0 : ℝ) (y v : E) (hγ : ContDiffAt ℝ ∞ γ t0) (hc : ContDiffAt ℝ ∞ F y)
    (hγ0 : γ t0 = y) (hγ1 : deriv γ t0 = v) :
    deriv (deriv (F ∘ γ)) t0 =
      fderiv ℝ (fun x => fderiv ℝ F x v) y v + fderiv ℝ F y (deriv (deriv γ) t0) := by sorry
