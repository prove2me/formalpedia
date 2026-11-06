-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_clock_projected_variation
-- name    : BianchiIX.hasDerivAt_clock_projected_variation
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:27:35.482333+00:00
-- url     : https://prove2.me/theorems/02367388-383e-4679-850b-f0b926fd5a2d
-- title:
--   Removing the variation of the clock from a nonautonomous equation
-- statement:
--   Let $E$ be a real normed space and $V:\mathbb R\times E\to E$
--   have derivative $J$ at $(\theta(t),Y(t))$. Let
--   $\theta,\delta\theta:\mathbb R\to\mathbb R$ and
--   $Y,\delta Y:\mathbb R\to E$ satisfy, at the fixed time $t$,
--   $$\theta'=a,\qquad Y'=aV(\theta,Y),\qquad
--   (\delta\theta)'=b,\qquad
--   (\delta Y)'=bV(\theta,Y)+aJ(\delta\theta,\delta Y).$$
--   Then $Z(s)=\delta Y(s)-\delta\theta(s)V(\theta(s),Y(s))$ has derivative
--   $$Z'(t)=aJ(0,Z(t)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ClockVariation.lean#L35-L60

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

theorem BianchiIX.hasDerivAt_clock_projected_variation
    {field : ℝ × E → E} {J : (ℝ × E) →L[ℝ] E}
    {theta dtheta : ℝ → ℝ} {Y dY : ℝ → E} {a b t : ℝ}
    (hfield : HasFDerivAt field J (theta t, Y t))
    (htheta : HasDerivAt theta a t)
    (hY : HasDerivAt Y (a • field (theta t, Y t)) t)
    (hdtheta : HasDerivAt dtheta b t)
    (hdY : HasDerivAt dY
      (b • field (theta t, Y t) + a • J (dtheta t, dY t)) t) :
    HasDerivAt (fun s => dY s - dtheta s • field (theta s, Y s))
      (a • J (0, dY t - dtheta t • field (theta t, Y t))) t := by sorry
