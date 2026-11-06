-- Prove2me | Theorems.Thm_BianchiIX_fderiv_variable_endpoint
-- name    : BianchiIX.fderiv_variable_endpoint
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:55:20.975899+00:00
-- url     : https://prove2.me/theorems/06855b8b-b0f9-4844-acb1-f650964fad4e
-- title:
--   The chain rule for a scalar function evaluated at a moving endpoint
-- statement:
--   Let $E$ be a real normed space, $F:E\times\mathbb R\to\mathbb R$,
--   and $\tau:E\to\mathbb R$. Suppose $F$ is differentiable at $(x,\tau(x))$
--   and $\tau$ at $x$. If the state slice $y\mapsto F(y,\tau(x))$ has
--   Frechet derivative $A$ at $x$, and the time slice $t\mapsto F(x,t)$
--   has derivative $b$ at $\tau(x)$, then
--   $$d\bigl(y\mapsto F(y,\tau(y))\bigr)_xv=Av+b\,d\tau_xv.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/MovingIntegralDerivative.lean#L14-L32

import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BianchiIX.fderiv_variable_endpoint {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E}
    {A : E →L[ℝ] ℝ} {b : ℝ} (hF : DifferentiableAt ℝ F (x, τ x))
    (hτ : DifferentiableAt ℝ τ x) (hleft : HasFDerivAt (fun y => F (y, τ x)) A x)
    (hright : HasDerivAt (fun t => F (x, t)) b (τ x)) (v : E) :
    fderiv ℝ (fun y => F (y, τ y)) x v = A v + b * fderiv ℝ τ x v := by sorry
