-- Prove2me | Theorems.Thm_CustomerVoice_OLearn_lambdaH1_le_lambdaH2_iff
-- name    : CustomerVoice.OLearn.lambdaH1_le_lambdaH2_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:08:05.428974+00:00
-- url     : https://prove2.me/theorems/48a6ced2-dc70-40ae-856f-c2efb439a3ef
-- title:
--   Appendix, Proof of Proposition 3, p. 28 — ΛH1 ≤ ΛH2 if and only if γ ≤ s/k
-- statement:
--   Under the standing assumptions,
--   $$\Lambda_{H1}=\frac{\gamma(s+k)}{(1-\gamma)s}\ \le\ \Lambda_{H2}=\frac{1+\gamma}{1-\gamma}\iff \gamma\le \frac{s}{k}.$$
--
--   This identifies which of the two high-type thresholds enters $\Lambda=\max\{\min\{\Lambda_{H1},\Lambda_{H2}\},\Lambda_L\}$ in each regime, and closes the proof of Proposition 3.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 28, Appendix, Proof of Proposition 3

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

namespace CustomerVoice.OLearn

theorem lambdaH1_le_lambdaH2_iff (M : Model) (hM : M.Standing) :
    M.LambdaH1 ≤ M.LambdaH2 ↔ M.γ ≤ M.s / M.k := by sorry

end CustomerVoice.OLearn
