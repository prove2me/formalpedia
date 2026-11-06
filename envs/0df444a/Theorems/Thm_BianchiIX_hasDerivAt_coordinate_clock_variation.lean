-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_coordinate_clock_variation
-- name    : BianchiIX.hasDerivAt_coordinate_clock_variation
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:32:46.436309+00:00
-- url     : https://prove2.me/theorems/97f91d7e-6e2f-4c3c-bfe9-adbec7267189
-- title:
--   The variational equation at a fixed observable clock
-- statement:
--   Let $E,F$ be real normed spaces, $p:E\to F$,
--   $c,a:E\to\mathbb R$, $f:E\to E$, $V:\mathbb R\times F\to F$, and
--   $\alpha,v:\mathbb R\to E$. At $x=\alpha(t)$ assume that $p,c$ are
--   $C^2$, $f,a$ are differentiable, and $V$ is differentiable at $(c(x),p(x))$.
--   Suppose
--   $$\alpha'(t)=f(x),\qquad v'(t)=df_xv(t),$$
--   and, for all $y$ sufficiently near $x$,
--   $$dc_yf(y)=a(y),\qquad dp_yf(y)=a(y)V(c(y),p(y)).$$
--   Define
--   $$Z(s)=dp_{\alpha(s)}v(s)-dc_{\alpha(s)}v(s)
--   V(c(\alpha(s)),p(\alpha(s))).$$
--   Then
--   $$Z'(t)=a(x)\,d[V(c(x),\cdot)]_{p(x)}Z(t).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ClockVariation.lean#L62-L108

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BianchiIX.hasDerivAt_coordinate_clock_variation
    {p : E → F} {clock rate : E → ℝ} {f : E → E} {field : ℝ × F → F}
    {alpha v : ℝ → E} {t : ℝ}
    (hp : ContDiffAt ℝ 2 p (alpha t)) (hc : ContDiffAt ℝ 2 clock (alpha t))
    (hf : DifferentiableAt ℝ f (alpha t)) (hr : DifferentiableAt ℝ rate (alpha t))
    (hfield : DifferentiableAt ℝ field (clock (alpha t), p (alpha t)))
    (ha : HasDerivAt alpha (f (alpha t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (alpha t) (v t)) t)
    (hclock : (fun x => fderiv ℝ clock x (f x)) =ᶠ[𝓝 (alpha t)] rate)
    (hstate : (fun x => fderiv ℝ p x (f x)) =ᶠ[𝓝 (alpha t)]
      (fun x => rate x • field (clock x, p x))) :
    HasDerivAt (fun s => fderiv ℝ p (alpha s) (v s) -
      fderiv ℝ clock (alpha s) (v s) • field (clock (alpha s), p (alpha s)))
      (rate (alpha t) • fderiv ℝ (fun Y => field (clock (alpha t), Y)) (p (alpha t))
        (fderiv ℝ p (alpha t) (v t) -
          fderiv ℝ clock (alpha t) (v t) • field (clock (alpha t), p (alpha t)))) t := by sorry
