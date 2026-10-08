-- Prove2me | Theorems.Thm_CVPricing_CertEquiv_induction_on_eventA
-- name    : CVPricing.CertEquiv.induction_on_eventA
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:36:53.124492+00:00
-- url     : https://prove2.me/theorems/8210c959-7efe-4c77-9a79-1589c4279dda
-- title:
--   Proof of Proposition 1, pp. 780–781 — on the event $A$, $p_{t+1} = p_h$ for all $t \ge 2$
-- statement:
--   Consider the model of `CVPricing.CertEquiv.Model`, initial prices $p_l \le p_1 < p_2 \le p_h$, a number $\delta > 0$, and a noise path $(e_i)_{i \ge 1}$ that lies in the event $A_\delta$ of `CVPricing.CertEquiv.EventA`. Then the certainty equivalent price path driven by $(e_i)$ satisfies
--
--   $$p_{t+1} = p_h \qquad \text{for all } t \ge 2 .$$
--
--   This is the deterministic heart of Proposition 1: once the first two noise values push the fitted line far enough and the later running means of the noise stay in the band $[-\delta, \delta]$, the estimated optimal price never falls below $p_h$ again.
--
--   **Formalization Note** The statement is about a single noise path; no probability is involved. It uses the corrected event $A$ (factor $\delta$ restored in its second line). The proof assumes $p_1 < p_2$ without loss of generality. It uses $p_{\mathrm{opt}} < p_h$, which is a field of the model.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), pp. 780–781 (PDF 12–13), Appendix, proof of Proposition 1, 'We show by induction that on the event A, p_{t+1} = p_h for all t ≥ 2.'

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_CEPrice
import Definitions.Def_CVPricing_CertEquiv_EventA

namespace CVPricing.CertEquiv

theorem induction_on_eventA (M : Model) {p₁ p₂ : ℝ} (hp₁ : p₁ ∈ Set.Icc M.pl M.ph)
    (hp₂ : p₂ ∈ Set.Icc M.pl M.ph) (h12 : p₁ < p₂) {δ : ℝ} (hδ : 0 < δ) (e : ℕ → ℝ)
    (hA : EventA M p₁ p₂ δ e) :
    ∀ t : ℕ, 2 ≤ t → cePrice M p₁ p₂ e (t + 1) = M.ph := by sorry

end CVPricing.CertEquiv
