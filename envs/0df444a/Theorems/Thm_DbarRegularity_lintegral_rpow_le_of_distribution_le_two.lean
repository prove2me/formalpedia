-- Prove2me | Theorems.Thm_DbarRegularity_lintegral_rpow_le_of_distribution_le_two
-- name    : DbarRegularity.lintegral_rpow_le_of_distribution_le_two
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:52:09.81835+00:00
-- url     : https://prove2.me/theorems/93fc4dac-74fa-4fdb-80cd-2733808ae8e9
-- title:
--   A two-term distribution bound by the large and small values of h gives an L^p bound for 1 < p < r
-- statement:
--   Let $(X,\mu)$ be an s-finite measure space, let $g,h:X\to[0,\infty]$ be $\mu$-a.e. measurable, let $1<p<r<\infty$ be real, let $C,D\in[0,\infty]$, and suppose that for every $t>0$
--   $$\mu\{x: g(x)>t\}\le\frac{C}{t}\int_{\{x:\,h(x)>t\}}h\,d\mu+\Big(\frac{D}{t}\Big)^{r}\int_{\{x:\,h(x)\le t\}}h^{r}\,d\mu.$$
--   Then
--   $$\int_X g^p\,d\mu\le\Big(C\,\frac{p}{p-1}+D^{r}\,\frac{p}{r-p}\Big)\int_X h^p\,d\mu.$$
--
--   This converts a two-term distribution-function estimate, controlled by the large values of $h$ in the first term and by the small values of $h$ in the second, into a strong $L^p$ bound with an explicit constant, for every exponent $p$ strictly between $1$ and $r$.
--
--   **Formalization Note.** $g,h$ are `ℝ≥0∞`-valued and `AEMeasurable`; $t$ ranges over `ℝ≥0` with $t>0$; $p,r$ are real; powers are `ℝ≥0∞` real powers and integrals are lower Lebesgue integrals `∫⁻`. The integrals over $\{h>t\}$ and $\{h\le t\}$ are written with `Set.indicator`. No finiteness of $g$ or of the integrals is assumed; when $C$ or $D$ is $\infty$, or $\int h^p=\infty$, the conclusion may be trivial.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 4.2, Theorem 5, p. 21

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

/-- Let `g, h ≥ 0` on an s-finite measure space and `1 < p < r`. If for every `t > 0`
`μ{g > t} ≤ (C/t) ∫_{h > t} h + (D/t)^r ∫_{h ≤ t} h^r`, then
`∫ g^p ≤ (C p/(p-1) + D^r p/(r-p)) ∫ h^p`. -/
theorem lintegral_rpow_le_of_distribution_le_two {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {g h : X → ℝ≥0∞} (hg : AEMeasurable g μ) (hh : AEMeasurable h μ)
    {p r : ℝ} (hp : 1 < p) (hpr : p < r) (C D : ℝ≥0∞)
    (H : ∀ t : ℝ≥0, 0 < t → μ {x | (t : ℝ≥0∞) < g x} ≤
      C / t * ∫⁻ x, {x | (t : ℝ≥0∞) < h x}.indicator h x ∂μ +
      (D / t) ^ r * ∫⁻ x, {x | h x ≤ t}.indicator (fun x => h x ^ r) x ∂μ) :
    ∫⁻ x, g x ^ p ∂μ ≤
      (C * ENNReal.ofReal (p / (p - 1)) + D ^ r * ENNReal.ofReal (p / (r - p))) *
        ∫⁻ x, h x ^ p ∂μ := by sorry

end DbarRegularity
