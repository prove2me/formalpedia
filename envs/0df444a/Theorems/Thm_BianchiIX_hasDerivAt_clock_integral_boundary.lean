-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_clock_integral_boundary
-- name    : BianchiIX.hasDerivAt_clock_integral_boundary
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:56:33.685887+00:00
-- url     : https://prove2.me/theorems/6a3ccbce-8c2c-4dbc-a3b9-d1c576d997a8
-- title:
--   Clock motion in an integral variation is an exact boundary derivative
-- statement:
--   Let $E,F$ be real normed spaces,
--   $\alpha,v:\mathbb R\to E$, $p:E\to F$, $c,r:E\to\mathbb R$,
--   $f:E\to E$, and $L:\mathbb R\times F\to\mathbb R$. Put $x=\alpha(t)$.
--   Assume $p,f,r$ are differentiable at $x$, $c$ is $C^2$ there, and
--   $L$ is differentiable at $(c(x),p(x))$. Suppose
--   $$\alpha'(t)=f(x),\qquad v'(t)=df_xv(t),\qquad
--   dc_qf(q)=r(q)\text{ for }q\text{ near }x,$$
--   and $dp_xf(x)=r(x)h$ for some $h\in F$. Set
--   $w=dp_xv(t)-dc_xv(t)h$ and
--   $$B(s)=L(c(\alpha(s)),p(\alpha(s)))\,dc_{\alpha(s)}v(s).$$
--   Then
--   $$B'(t)=d\bigl(r\,L(c,p)\bigr)_xv(t)
--   -r(x)d_2L(c(x),p(x))w.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ClockIntegralVariation.lean#L15-L62

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BianchiIX.hasDerivAt_clock_integral_boundary
    {p : E → F} {clock rate : E → ℝ} {f : E → E} {L : ℝ × F → ℝ}
    {alpha v : ℝ → E} {field : F} {t : ℝ}
    (hp : DifferentiableAt ℝ p (alpha t)) (hc : ContDiffAt ℝ 2 clock (alpha t))
    (hf : DifferentiableAt ℝ f (alpha t)) (hr : DifferentiableAt ℝ rate (alpha t))
    (hL : DifferentiableAt ℝ L (clock (alpha t), p (alpha t)))
    (ha : HasDerivAt alpha (f (alpha t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (alpha t) (v t)) t)
    (hclock : (fun x => fderiv ℝ clock x (f x)) =ᶠ[𝓝 (alpha t)] rate)
    (hstate : fderiv ℝ p (alpha t) (f (alpha t)) = rate (alpha t) • field) :
    HasDerivAt (fun s => L (clock (alpha s), p (alpha s)) * fderiv ℝ clock (alpha s) (v s))
      (fderiv ℝ (fun x => rate x * L (clock x, p x)) (alpha t) (v t) -
        rate (alpha t) * fderiv ℝ (fun Y => L (clock (alpha t), Y)) (p (alpha t))
          (fderiv ℝ p (alpha t) (v t) - fderiv ℝ clock (alpha t) (v t) • field)) t := by sorry
