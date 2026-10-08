-- Prove2me | Theorems.Thm_CVPricing_CertEquiv_case_t_two
-- name    : CVPricing.CertEquiv.case_t_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:35:18.355586+00:00
-- url     : https://prove2.me/theorems/36217243-fff6-4ee5-8513-e00ea4678709
-- title:
--   Proof of Proposition 1, Case t = 2, p. 780 — the first line fit, and the first condition of $A$ forces $p_3 = p_h$
-- statement:
--   Consider the model of `CVPricing.CertEquiv.Model`, initial prices $p_l \le p_1 < p_2 \le p_h$ and any noise path $(e_i)$. The least squares line through the two observations $(p_i,\ a_0^{(0)} + a_1^{(0)}p_i + e_i)$, $i = 1, 2$, has slope and intercept
--
--   $$\hat a_{12} = a_1^{(0)} + \frac{e_2 - e_1}{p_2 - p_1}, \qquad \hat a_{02} = a_0^{(0)} + \frac{e_1 p_2 - e_2 p_1}{p_2 - p_1}.$$
--
--   Moreover, if
--
--   $$(p_2 - 2p_h)e_1 + (2p_h - p_1)e_2 \ \ge\ -a_1^{(0)}(p_2 - p_1)\,2p_h ,$$
--
--   then the certainty equivalent price of period 3 is $p_3 = p_h$.
--
--   This is the base case of the induction showing that on the event $A$ all prices from period 3 on equal $p_h$.
--
--   **Formalization Note** The paper prints the intercept as $\hat a_{02} = (e_1p_2 - e_2p_1)(p_2 - p_1)^{-1}$, omitting $a_0^{(0)}$; the line through the two points has the intercept stated here. With the correct intercept, $p_3 = p_h$ is equivalent to $a_0^{(0)}(p_2 - p_1) + (p_2 - 2p_h)e_1 + (2p_h - p_1)e_2 \ge -a_1^{(0)}(p_2 - p_1)2p_h$; since $a_0^{(0)}(p_2 - p_1) > 0$, the printed condition is sufficient, which is the implication stated. The proof assumes $p_1 < p_2$ without loss of generality.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 780 (PDF 12), Appendix, proof of Proposition 1, Case t = 2

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_CEPrice

namespace CVPricing.CertEquiv

open KeskinZeevi.SufficientConditions

theorem case_t_two (M : Model) {p₁ p₂ : ℝ} (hp₁ : p₁ ∈ Set.Icc M.pl M.ph)
    (hp₂ : p₂ ∈ Set.Icc M.pl M.ph) (h12 : p₁ < p₂) (e : ℕ → ℝ) :
    lsEstimateOf (cePrice M p₁ p₂ e) (demandOf M (cePrice M p₁ p₂ e) e) 2 =
        (M.a₀ + (e 1 * p₂ - e 2 * p₁) / (p₂ - p₁), M.a₁ + (e 2 - e 1) / (p₂ - p₁)) ∧
      (-M.a₁ * (p₂ - p₁) * (2 * M.ph) ≤ (p₂ - 2 * M.ph) * e 1 + (2 * M.ph - p₁) * e 2 →
        cePrice M p₁ p₂ e 3 = M.ph) := by sorry

end CVPricing.CertEquiv
