-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_observable_variation
-- name    : BianchiIX.hasDerivAt_observable_variation
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:27:34.554405+00:00
-- url     : https://prove2.me/theorems/09d256f9-dadd-47b9-991f-c23a7c9c13a4
-- title:
--   Differentiating the variation of an observable
-- statement:
--   Let $E,F$ be real normed spaces, $p:E\to F$,
--   $f:E\to E$, and $\alpha,v:\mathbb R\to E$. Fix $t\in\mathbb R$.
--   Assume $p$ is $C^2$ and $f$ is differentiable at $\alpha(t)$, with
--   $$\alpha'(t)=f(\alpha(t)),\qquad v'(t)=df_{\alpha(t)}v(t).$$
--   Then
--   $$\left.\frac{d}{ds}\bigl(dp_{\alpha(s)}v(s)\bigr)\right|_{s=t}
--   =d\bigl[x\mapsto dp_xf(x)\bigr]_{\alpha(t)}v(t).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ClockVariation.lean#L15-L33

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

theorem BianchiIX.hasDerivAt_observable_variation
    {p : E → F} {f : E → E} {alpha v : ℝ → E} {t : ℝ}
    (hp : ContDiffAt ℝ 2 p (alpha t)) (hf : DifferentiableAt ℝ f (alpha t))
    (ha : HasDerivAt alpha (f (alpha t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (alpha t) (v t)) t) :
    HasDerivAt (fun s => fderiv ℝ p (alpha s) (v s))
      (fderiv ℝ (fun x => fderiv ℝ p x (f x)) (alpha t) (v t)) t := by sorry
