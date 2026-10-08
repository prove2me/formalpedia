-- Prove2me | Theorems.Thm_CVPricing_CertEquiv_kolmogorov_dyadic_bound
-- name    : CVPricing.CertEquiv.kolmogorov_dyadic_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T09:49:00.568767+00:00
-- url     : https://prove2.me/theorems/28e4d612-6f15-4f52-a0ff-56a13565c6f1
-- title:
--   Proof of Proposition 1, p. 780 — $P(\sup_{t\ge3}|(t-2)^{-1}\sum_{i=3}^t e_i| > \epsilon) \le 8\sigma^2\epsilon^{-2} < 1$
-- statement:
--   Let $e_1, e_2, \dots$ be independent $N(0, \sigma^2)$ random variables with $\sigma > 0$. For every $\epsilon > \sqrt 8\,\sigma$,
--
--   $$P\Big(\sup_{t \ge 3} \Big|\frac{1}{t-2}\sum_{i=3}^t e_i\Big| > \epsilon\Big) \ \le\ 8\sigma^2\epsilon^{-2} \ <\ 1 .$$
--
--   The paper derives this from Kolmogorov's maximal inequality applied on the dyadic blocks $2^j < t \le 2^{j+1}$. It shows that the running means of the noise after period 2 stay in a bounded band with positive probability, which is the third condition of the event $A$.
--
--   **Formalization Note** The noise is the referenced `RobustBooking.Shared.GaussianNoise`, whose Lean index $k$ is period $k+1$, so the paper's $e_i$ is `ε (i - 1)`. The supremum exceeding $\epsilon$ is written as the existence of some $t \ge 3$ with the term exceeding $\epsilon$. The paper's noise is the conditional deviation $e_t = D(p_t) - E[D(p_t) \mid \text{past}]$, which in the Gaussian model of Proposition 1 is i.i.d. $N(0,\sigma^2)$.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 780 (PDF 12), Appendix, proof of Proposition 1, the display following 'It follows from the Kolmogorov inequality'

import Mathlib
import Definitions.Def_RobustBooking_Shared_GaussianNoise

namespace CVPricing.CertEquiv

open MeasureTheory ProbabilityTheory

theorem kolmogorov_dyadic_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {σ : ℝ} (hσ : 0 < σ) {ε : ℕ → Ω → ℝ}
    (hε : RobustBooking.Shared.GaussianNoise σ P ε) {η : ℝ} (hη : Real.sqrt 8 * σ < η) :
    P {ω | ∃ t : ℕ, 3 ≤ t ∧
        η < |(1 / ((t : ℝ) - 2)) * ∑ i ∈ Finset.Icc 3 t, ε (i - 1) ω|} ≤
        ENNReal.ofReal (8 * σ ^ 2 * η⁻¹ ^ 2) ∧
      8 * σ ^ 2 * η⁻¹ ^ 2 < 1 := by sorry

end CVPricing.CertEquiv
