-- Prove2me | Theorems.Thm_CVPricing_CertEquiv_ce_pricing_inconsistent
-- name    : CVPricing.CertEquiv.ce_pricing_inconsistent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:35:53.678053+00:00
-- url     : https://prove2.me/theorems/c91fb17d-e632-4930-a8ee-429230242f0d
-- title:
--   Proposition 1 — certainty equivalent pricing fails to converge to $p_{\mathrm{opt}}$ with positive probability
-- statement:
--   Suppose demand is normally distributed with constant variance and expected demand linear in the price: in period $t$ the demand is $d_t = a_0^{(0)} + a_1^{(0)}p_t + e_t$, where $e_1, e_2, \dots$ are independent $N(0, \sigma^2)$ random variables on a probability space $(\Omega, P)$, and the parameters satisfy the standing assumptions of `CVPricing.CertEquiv.Model`: $0 < p_l < p_h$, $\sigma > 0$, $a_0^{(0)} > 0$, $a_1^{(0)} < 0$, $a_0^{(0)} + a_1^{(0)}p_h \ge 0$ and $p_l < p_{\mathrm{opt}} < p_h$ with $p_{\mathrm{opt}} = -a_0^{(0)}/(2a_1^{(0)})$. Let the prices $(p_t)$ be set by certainty equivalent pricing from two different initial prices $p_1 \ne p_2$ in $[p_l, p_h]$. Then
--
--   $$P\big(p_t \not\to p_{\mathrm{opt}} \text{ as } t \to \infty\big) > 0 .$$
--
--   Certainty equivalent (myopic) pricing is therefore not strongly consistent: with positive probability the prices it charges do not converge to the optimal price. This is the paper's motivation for controlled variance pricing.
--
--   **Formalization Note** The certainty equivalent rule is `cePrice`, which uses the convention of the paper's proof that $p_{t+1} = p_h$ whenever the estimated slope $\hat a_{1t}$ is nonnegative. The paper's $e_i$ is `ε (i - 1)` (the referenced noise is indexed from $0$). The event is written as the set of outcomes whose price path does not tend to $p_{\mathrm{opt}}$; its measurability is not asserted.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 775 (PDF 7), Proposition 1

import Mathlib
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_CVPricing_CertEquiv_CEPrice

namespace CVPricing.CertEquiv

open MeasureTheory ProbabilityTheory Filter Topology

theorem ce_pricing_inconsistent (M : Model) {p₁ p₂ : ℝ} (hp₁ : p₁ ∈ Set.Icc M.pl M.ph)
    (hp₂ : p₂ ∈ Set.Icc M.pl M.ph) (hne : p₁ ≠ p₂)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ε : ℕ → Ω → ℝ} (hε : RobustBooking.Shared.GaussianNoise M.σ P ε) :
    0 < P {ω | ¬ Tendsto (fun t => cePrice M p₁ p₂ (fun i => ε (i - 1) ω) t) atTop
      (𝓝 (optPrice M))} := by sorry

end CVPricing.CertEquiv
