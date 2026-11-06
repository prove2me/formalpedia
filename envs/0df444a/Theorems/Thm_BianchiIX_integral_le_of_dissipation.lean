-- Prove2me | Theorems.Thm_BianchiIX_integral_le_of_dissipation
-- name    : BianchiIX.integral_le_of_dissipation
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:47:32.763912+00:00
-- url     : https://prove2.me/theorems/462b0bb8-c7e0-4778-a627-568bd0d510ff
-- title:
--   A dissipative derivative controls the accumulated forcing
-- statement:
--   Let $a\leq b$, $c>0$, and let $f$ have derivative $q(t)$
--   on $[a,b]$. If $g$ is continuous there, $q(t)\leq-cg(t)$ on the interval,
--   and $f(b)\geq0$, then $\int_a^b g(t)\,dt\leq f(a)/c$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/DissipationBudget.lean#L10-L26

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.integral_le_of_dissipation {f f' g : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ContinuousOn g (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f' t ≤ -c * g t) (hfb : 0 ≤ f b) :
    (∫ t in a..b, g t) ≤ f a / c := by sorry
