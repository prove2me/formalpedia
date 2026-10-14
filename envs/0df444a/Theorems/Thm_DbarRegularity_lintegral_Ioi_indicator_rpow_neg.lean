-- Prove2me | Theorems.Thm_DbarRegularity_lintegral_Ioi_indicator_rpow_neg
-- name    : DbarRegularity.lintegral_Ioi_indicator_rpow_neg
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:46:16.356987+00:00
-- url     : https://prove2.me/theorems/1c629cb3-ab2b-4de2-b900-f00b01494a8c
-- title:
--   The tail integral of s t^(-s-1) over [a, ∞) equals a^(-s) for every a in [0, ∞]
-- statement:
--   For every $a\in[0,\infty]$ and every real $s>0$,
--   $$\int_{\{t>0\,:\,t\ge a\}} s\,t^{-s-1}\,dt=a^{-s},$$
--   where the integral is a Lebesgue integral on $(0,\infty)$ with values in $[0,\infty]$, and $0^{-s}=\infty$, $\infty^{-s}=0$.
--
--   This is the tail companion of the power integral $\int_{\{0<t<a\}} q\,t^{q-1}\,dt=a^q$: it holds uniformly in $a$, including $a=0$ and $a=\infty$, so it can be applied pointwise to $[0,\infty]$-valued functions.
--
--   **Formalization Note.** $a$ is in `ℝ≥0∞`; the domain $\{t>0: t\ge a\}$ is written as the indicator of `{t : ℝ | a ≤ ENNReal.ofReal t}` integrated over `Ioi 0` with respect to Lebesgue measure on ℝ, and the integrand is `ENNReal.ofReal (s * t ^ (-s - 1))`. The right side is the `ℝ≥0∞` real power `a ^ (-s)`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 4.2, p. 21

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace DbarRegularity

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-- `∫_{t > 0, t ≥ a} s t^(-s-1) dt = a^(-s)` for every `a ∈ [0, ∞]` and `s > 0`
(as a lower Lebesgue integral in `[0, ∞]`, with `0^(-s) = ∞` and `∞^(-s) = 0`). -/
theorem lintegral_Ioi_indicator_rpow_neg (a : ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | a ≤ ENNReal.ofReal t}.indicator
      (fun t => ENNReal.ofReal (s * t ^ (-s - 1))) t = a ^ (-s) := by sorry

end DbarRegularity
