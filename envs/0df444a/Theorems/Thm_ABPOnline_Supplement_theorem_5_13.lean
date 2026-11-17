-- Prove2me | Theorems.Thm_ABPOnline_Supplement_theorem_5_13
-- name    : ABPOnline.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:37:25.8182+00:00
-- url     : https://prove2.me/theorems/0615a483-31d7-4371-bc3a-56156893cc00
-- title:
--   Theorem 5.13 — large negative margin, $E_\star(-K)\asymp K^2q_K$ and $\alpha_{\mathrm{on}}(\kappa)=\Theta(1/(\kappa^2\Phi(\kappa)))$
-- statement:
--   Let $\Phi$ be the standard normal distribution function, $K:=-\kappa$, $q_K:=\Phi(-K)$, and
--   $$
--   I_0:=\int_0^\infty\sqrt{2\Phi\big(-\sqrt{s/2}\big)}\,ds .
--   $$
--   As $K\to\infty$,
--   $$
--   \big(I_0^{-2}+o(1)\big)K^2q_K\le E_\star(-K)\le(4+o(1))K^2q_K,
--   $$
--   and consequently
--   $$
--   \frac{1/(2\pi)+o(1)}{K^2q_K}\le\alpha_{\mathrm{on}}(-K)\le\frac{2I_0^2/\pi+o(1)}{K^2q_K}.
--   $$
--   In particular, $\alpha_{\mathrm{on}}(\kappa)=\Theta\big(1/(\kappa^2\Phi(\kappa))\big)$ as $\kappa\to-\infty$.
--
--   The online threshold therefore grows like $1/(\kappa^2\Phi(\kappa))$ for very negative margins, with explicit two-sided constants.
--
--   **Formalization Note** Each $o(1)$ is a function of $K$ that tends to $0$ as $K\to\infty$ (one for each side), and each pair of bounds holds for all sufficiently large $K$. The $\Theta$ statement is the existence of constants $c>0$ and $C>0$ with $c/(\kappa^2\Phi(\kappa))\le\alpha_{\mathrm{on}}(\kappa)\le C/(\kappa^2\Phi(\kappa))$ for all sufficiently negative $\kappa$. $E_\star$ and $\alpha_{\mathrm{on}}$ are extended nonnegative reals.
--
--   Differences from the source:
--   - generalization: E⋆ defined from a standard Brownian motion B = (B_t)_{0≤t≤1} with its completed natural filtration → the statement holds for every process B with IsBrownianOn1 B P on every probability space, with E⋆ computed on that B; reason: E⋆ depends only on the law of B; the source's Brownian motion is one such process
--   - encoding: o(1) terms and Θ as K → ∞, κ → −∞ → functions f, g with f, g → 0 as K → ∞ and the bounds for all sufficiently large K (∀ᶠ K in atTop); Θ as ∃ c, C > 0 with both bounds for all sufficiently negative κ (∀ᶠ κ in atBot); reason: the standard meaning of o(1) and Θ
--   - encoding: E⋆(−K), α_on(−K) real numbers → E⋆ and α_on in ℝ≥0∞, compared with ENNReal.ofReal of the real bounds; reason: the same inequalities
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), §5.3, (56), Theorem 5.13, (57)–(58), p.25 (PDF p.26)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1
import Definitions.Def_ABPOnline_Estar
import Definitions.Def_ABPOnline_alphaOn
import Definitions.Def_ABPOnline_Supplement_I0

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ABPOnline.Supplement

/-- **Theorem 5.13 (Large negative margin)** (Jo–Lee, arXiv:2609.02124, printed p.25, PDF p.26).
With `K := −κ` and `q_K := Φ(−K)`, as `K → ∞`,
`(I₀⁻² + o(1)) K² q_K ≤ E⋆(−K) ≤ (4 + o(1)) K² q_K` (57), and consequently
`(1/(2π) + o(1))/(K² q_K) ≤ α_on(−K) ≤ (2I₀²/π + o(1))/(K² q_K)` (58). In particular
`α_on(κ) = Θ(1/(κ²Φ(κ)))` as `κ → −∞`.

**Formalization Note** `Φ` is Mathlib's `cdf (gaussianReal 0 1)`; `I₀` is `I0` of (56). Each `o(1)`
is a function of `K` tending to `0` as `K → ∞` (one per side), and each display holds for all
sufficiently large `K` (`∀ᶠ K in atTop`). `Θ` is: there are constants `0 < c, C` with
`c/(κ²Φ(κ)) ≤ α_on(κ) ≤ C/(κ²Φ(κ))` for all sufficiently negative `κ` (`∀ᶠ κ in atBot`). `E⋆` is
the published `ABPOnline.Estar` on an arbitrary standard Brownian motion on `[0,1]`, `α_on` the
published `ABPOnline.alphaOn`; both are in `ℝ≥0∞` and compared with `ENNReal.ofReal` of the real
bounds. -/
theorem theorem_5_13 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianOn1 B P) :
    (∃ f g : ℝ → ℝ, Tendsto f atTop (𝓝 0) ∧ Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ K in atTop,
        ENNReal.ofReal (((I0 ^ 2)⁻¹ + f K) * (K ^ 2 * cdf (gaussianReal 0 1) (-K))) ≤
            Estar P B (-K) ∧
          Estar P B (-K) ≤ ENNReal.ofReal ((4 + g K) * (K ^ 2 * cdf (gaussianReal 0 1) (-K)))) ∧
    (∃ f g : ℝ → ℝ, Tendsto f atTop (𝓝 0) ∧ Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ K in atTop,
        ENNReal.ofReal ((1 / (2 * Real.pi) + f K) / (K ^ 2 * cdf (gaussianReal 0 1) (-K))) ≤
            alphaOn (-K) ∧
          alphaOn (-K) ≤
            ENNReal.ofReal ((2 * I0 ^ 2 / Real.pi + g K) / (K ^ 2 * cdf (gaussianReal 0 1) (-K)))) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ κ in atBot,
        ENNReal.ofReal (c / (κ ^ 2 * cdf (gaussianReal 0 1) κ)) ≤ alphaOn κ ∧
          alphaOn κ ≤ ENNReal.ofReal (C / (κ ^ 2 * cdf (gaussianReal 0 1) κ))) := by sorry

end ABPOnline.Supplement
