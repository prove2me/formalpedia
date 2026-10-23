-- Prove2me | Theorems.Thm_CustomerVoice_OLearn_ic_case_low
-- name    : CustomerVoice.OLearn.ic_case_low
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:08:11.062089+00:00
-- url     : https://prove2.me/theorems/d6ad10ee-77b2-47f4-91fb-13ecfffc9629
-- title:
--   Appendix, Proof of Proposition 3, p. 28 — for γ ≤ s/k, IC′_H ⇔ θH/θL ≥ ΛH1 and IC′_L ⇔ θH/θL ≥ ΛL
-- statement:
--   Under the standing assumptions, suppose $\gamma\le s/k$, so that $q^*(\theta)=\gamma\theta/(s+\gamma k)$. Then
--   $$\mathrm{IC}'_H \iff \frac{\theta_H}{\theta_L}\ge \Lambda_{H1}=\frac{\gamma(s+k)}{(1-\gamma)s},\qquad \mathrm{IC}'_L\iff\frac{\theta_H}{\theta_L}\ge\Lambda_L=\frac{s}{\gamma k}.$$
--
--   In this regime the two incentive constraints of (11)–(12) reduce to the two ratio thresholds that make up $\Lambda$.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 28, Appendix, Proof of Proposition 3

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

namespace CustomerVoice.OLearn

theorem ic_case_low (M : Model) (hM : M.Standing) (hγ : M.γ ≤ M.s / M.k) :
    (M.ICH' ↔ M.θH / M.θL ≥ M.LambdaH1) ∧ (M.ICL' ↔ M.θH / M.θL ≥ M.LambdaL) := by sorry

end CustomerVoice.OLearn
