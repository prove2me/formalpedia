-- Prove2me | Theorems.Thm_BianchiIX_fderiv_moving_intervalIntegral
-- name    : BianchiIX.fderiv_moving_intervalIntegral
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:57:19.861736+00:00
-- url     : https://prove2.me/theorems/84c977ce-bd6e-4bbf-805b-1e1223759740
-- title:
--   Leibniz's formula from joint regularity along the integration segment
-- statement:
--   Let $E$ be a real normed space, $F:E\times\mathbb R\to\mathbb R$,
--   and $\tau:E\to\mathbb R$. Suppose $\tau$ is $C^1$ at $x$,
--   $T=\tau(x)\geq0$, and $F$ is $C^1$ at $(x,t)$ for every $t\in[0,T]$.
--   Then, for every $v\in E$,
--   $$d\left(y\mapsto\int_0^{\tau(y)}F(y,t)\,dt\right)_xv
--   =\int_0^T dF_{(x,t)}(v,0)\,dt+F(x,T)d\tau_xv.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/MovingIntegralDerivative.lean#L55-L123

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

theorem BianchiIX.fderiv_moving_intervalIntegral {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E}
    (hτ : ContDiffAt ℝ 1 τ x) (hpos : 0 ≤ τ x)
    (hF : ∀ t ∈ Icc 0 (τ x), ContDiffAt ℝ 1 F (x, t)) (v : E) :
    fderiv ℝ (fun y => ∫ t in 0..τ y, F (y, t)) x v =
      (∫ t in 0..τ x, fderiv ℝ F (x, t) (v, 0)) + F (x, τ x) * fderiv ℝ τ x v := by sorry
