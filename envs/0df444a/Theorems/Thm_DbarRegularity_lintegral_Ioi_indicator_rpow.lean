-- Prove2me | Theorems.Thm_DbarRegularity_lintegral_Ioi_indicator_rpow
-- name    : DbarRegularity.lintegral_Ioi_indicator_rpow
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:54:52.112513+00:00
-- url     : https://prove2.me/theorems/2947b37c-eddc-49cb-ad5c-6c234ea795ff
-- title:
--   The power integral of q t^(q-1) over (0, a) equals a^q for every a in [0, ∞]
-- statement:
--   For every $a\in[0,\infty]$ and every real $q>0$,
--   $$\int_{\{t>0\,:\,t<a\}} q\,t^{q-1}\,dt=a^q,$$
--   where the integral is a Lebesgue integral on $(0,\infty)$ with values in $[0,\infty]$, and $\infty^q=\infty$.
--
--   This is the elementary power integral in the extended form needed for distribution-function identities: it holds uniformly in $a$, including $a=0$ and $a=\infty$, so it can be applied pointwise to $[0,\infty]$-valued functions.
--
--   **Formalization Note.** $a$ is in `ℝ≥0∞`; the domain $\{0<t<a\}$ is written as the indicator of `{t : ℝ | ENNReal.ofReal t < a}` integrated over `Ioi 0` with respect to Lebesgue measure on ℝ, and the integrand is `ENNReal.ofReal (q * t ^ (q - 1))`. The right side is the `ℝ≥0∞` real power `a ^ q`.
-- source:
--   Auxiliary statement for E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.2 and § 1.3, pp. 4 and 7 (distribution functions)

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal

/-- For every `a ∈ [0, ∞]` and every real `q > 0`,
`∫_{t > 0, t < a} q t^(q-1) dt = a^q` (as a lower Lebesgue integral in `[0, ∞]`). -/
theorem lintegral_Ioi_indicator_rpow (a : ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < a}.indicator
      (fun t => ENNReal.ofReal (q * t ^ (q - 1))) t = a ^ q := by sorry

end DbarRegularity
