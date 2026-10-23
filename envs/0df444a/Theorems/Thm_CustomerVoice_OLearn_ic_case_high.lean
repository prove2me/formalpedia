-- Prove2me | Theorems.Thm_CustomerVoice_OLearn_ic_case_high
-- name    : CustomerVoice.OLearn.ic_case_high
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:59.459841+00:00
-- url     : https://prove2.me/theorems/2571b4a4-dccb-4675-977f-2e3ee39b78a5
-- title:
--   Appendix, Proof of Proposition 3, p. 28 — for γ ≥ s/k, IC′_H ⇔ θH/θL ≥ ΛH2, and IC′_L holds strictly
-- statement:
--   Under the standing assumptions, suppose $\gamma\ge s/k$, so that $q^*(\theta)=\theta/(2k)$. Then
--   $$\mathrm{IC}'_H \iff \frac{\theta_H}{\theta_L}\ge\Lambda_{H2}=\frac{1+\gamma}{1-\gamma},\qquad \mu(q^*(\theta_L),\theta_L,\theta_L) > \mu(q^*(\theta_H),\theta_L,\theta_H).$$
--
--   In this regime the low type never wants to mimic the high type, and only the high type's constraint restricts the preference ratio.
--
--   **Formalization Note** "is always higher than" is rendered as a strict inequality, holding for all parameters in this regime.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 28, Appendix, Proof of Proposition 3

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

namespace CustomerVoice.OLearn

theorem ic_case_high (M : Model) (hM : M.Standing) (hγ : M.s / M.k ≤ M.γ) :
    (M.ICH' ↔ M.θH / M.θL ≥ M.LambdaH2) ∧
    M.mu (M.qO .H) M.θL M.θH < M.mu (M.qO .L) M.θL M.θL := by sorry

end CustomerVoice.OLearn
