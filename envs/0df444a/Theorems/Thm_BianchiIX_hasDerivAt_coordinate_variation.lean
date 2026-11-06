-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_coordinate_variation
-- name    : BianchiIX.hasDerivAt_coordinate_variation
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T22:42:18.177888+00:00
-- url     : https://prove2.me/theorems/0887520b-4524-42c1-be9e-d7f64c45182e
-- title:
--   Transport of a variational equation through a parameterized coordinate map
-- statement:
--   Let $E,F,G$ be real normed spaces, $p:E\to F$, $f:E\to E$,
--   $g:F\to F$, and $\alpha,v:\mathbb R\to E$. Fix $t\in\mathbb R$.
--   Assume $p$ is $C^2$ at $\alpha(t)$, $f$ is differentiable there, and
--   $g$ is differentiable at $p(\alpha(t))$, with
--   $$\alpha'(t)=f(\alpha(t)),\qquad v'(t)=df_{\alpha(t)}v(t).$$
--   Suppose $b:G\to E$ has derivative $B$ at $z\in G$, with
--   $b(z)=\alpha(t)$ and $Bw=v(t)$ for some $w\in G$, and
--   $$dp_{b(u)}f(b(u))=g(p(b(u)))$$
--   for all $u$ sufficiently near $z$. Then
--   $$\left.\frac{d}{ds}\bigl(dp_{\alpha(s)}v(s)\bigr)\right|_{s=t}
--   =dg_{p(\alpha(t))}\bigl(dp_{\alpha(t)}v(t)\bigr).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoordinateVariation.lean#L15-L46

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem BianchiIX.hasDerivAt_coordinate_variation
    {p : E → F} {f : E → E} {g : F → F} {alpha v : ℝ → E} {t : ℝ}
    (hp : ContDiffAt ℝ 2 p (alpha t)) (hf : DifferentiableAt ℝ f (alpha t))
    (hg : DifferentiableAt ℝ g (p (alpha t)))
    (ha : HasDerivAt alpha (f (alpha t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (alpha t) (v t)) t)
    {b : G → E} {B : G →L[ℝ] E} {z w : G}
    (hb : HasFDerivAt b B z) (hbz : b z = alpha t) (hBw : B w = v t)
    (heq : (fun q => fderiv ℝ p (b q) (f (b q))) =ᶠ[𝓝 z] (fun q => g (p (b q)))) :
    HasDerivAt (fun s => fderiv ℝ p (alpha s) (v s))
      (fderiv ℝ g (p (alpha t)) (fderiv ℝ p (alpha t) (v t))) t := by sorry
