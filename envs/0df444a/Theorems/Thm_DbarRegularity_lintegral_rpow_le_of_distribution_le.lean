-- Prove2me | Theorems.Thm_DbarRegularity_lintegral_rpow_le_of_distribution_le
-- name    : DbarRegularity.lintegral_rpow_le_of_distribution_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:54:51.377591+00:00
-- url     : https://prove2.me/theorems/6edc9d57-cee0-43c9-8405-1022ef4e9eaa
-- title:
--   A distribution bound by the large values of h gives an L^p bound for every p > 1
-- statement:
--   Let $(X,\mu)$ be an s-finite measure space, let $g,h:X\to[0,\infty]$ be $\mu$-a.e. measurable, let $C\in[0,\infty]$, and suppose that for every $t>0$
--   $$\mu\{x: g(x)>t\}\le\frac{C}{t}\int_{\{x:\,h(x)>t/2\}}h\,d\mu.$$
--   Then for every real $p>1$,
--   $$\int_X g^p\,d\mu\le 2^{p-1}\,C\,\frac{p}{p-1}\int_X h^p\,d\mu.$$
--
--   This converts a distribution-function estimate of the above form into a strong $L^p$ bound with an explicit constant, for every exponent $p>1$ at once.
--
--   **Formalization Note.** $g,h$ are `ℝ≥0∞`-valued and `AEMeasurable`; $t$ ranges over `ℝ≥0` with $t>0$; $p$ is real; powers are `ℝ≥0∞` real powers and integrals are lower Lebesgue integrals `∫⁻`. The integral over $\{h>t/2\}$ is written with `Set.indicator`. No finiteness of $g$ or of the integrals is assumed; when $C=\infty$ or $\int h^p=\infty$ the conclusion may be trivial.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, Theorem 1 (c), pp. 5–7

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

/-- If `μ{g > t} ≤ (C / t) ∫_{h > t/2} h dμ` for every `t > 0`, then for every `p > 1`,
`∫ g^p dμ ≤ 2^(p-1) · C · p/(p-1) · ∫ h^p dμ`. -/
theorem lintegral_rpow_le_of_distribution_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SFinite μ] {g h : X → ℝ≥0∞} (hg : AEMeasurable g μ) (hh : AEMeasurable h μ) {p : ℝ}
    (hp : 1 < p) (C : ℝ≥0∞)
    (H : ∀ t : ℝ≥0, 0 < t → μ {x | (t : ℝ≥0∞) < g x} ≤
      C / t * ∫⁻ x, {x | (t : ℝ≥0∞) / 2 < h x}.indicator h x ∂μ) :
    ∫⁻ x, g x ^ p ∂μ ≤ 2 ^ (p - 1) * C * ENNReal.ofReal (p / (p - 1)) * ∫⁻ x, h x ^ p ∂μ := by
  sorry

end DbarRegularity
