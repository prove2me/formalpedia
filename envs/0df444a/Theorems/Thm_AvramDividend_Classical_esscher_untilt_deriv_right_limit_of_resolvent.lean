-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_untilt_deriv_right_limit_of_resolvent
-- name    : AvramDividend.Classical.esscher_untilt_deriv_right_limit_of_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:54:09.464315+00:00
-- url     : https://prove2.me/theorems/8a8f9089-712f-4a9d-a2bf-4f896d0a4992
-- title:
--   Right-hand derivative limit preserved by the Esscher untilt
-- statement:
--   If W(x)=exp(phi*x)V(x) for x>0, with V(x)→0, V'(x)=g(x), and g continuous on nonnegative times with g(0)=s, then the ordinary derivatives W'(x) converge to s as x→0+. This supplies the final deterministic bridge from the positive Gaussian Volterra derivative resolvent to the original scale-function right derivative.
-- source:
--   Elementary real derivative product rule and continuity at zero; Gaussian Esscher normalisation.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set Filter
open scoped Topology

namespace AvramDividend.Classical
/-- A continuous Esscher derivative resolvent transfers its right limit to the original scale derivative. -/
theorem esscher_untilt_deriv_right_limit_of_resolvent
    (W V g : ℝ → ℝ) (φ s : ℝ)
    (hW : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hVlim : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hgcont : ContinuousOn g (Ici (0 : ℝ)))
    (hgzero : g 0 = s)
    (hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (g x) x) :
    Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
  sorry
end AvramDividend.Classical
