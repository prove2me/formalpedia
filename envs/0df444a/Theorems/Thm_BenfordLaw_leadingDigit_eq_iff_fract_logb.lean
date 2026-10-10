-- Prove2me | Theorems.Thm_BenfordLaw_leadingDigit_eq_iff_fract_logb
-- name    : BenfordLaw.leadingDigit_eq_iff_fract_logb
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:02.820926+00:00
-- url     : https://prove2.me/theorems/06c769f3-3f0f-40c5-85df-8ceb45fd3612
-- title:
--   Leading digit $d$ $\iff$ $\{\log_b x\} \in [\log_b d, \log_b(d+1))$
-- statement:
--   Let $b \ge 2$, let $x > 0$ be real and let $d \in \{1,\dots,b-1\}$. Then $x$ has leading digit $d$ in base $b$ if and only if the fractional part of $\log_b x$ lies in $[\log_b d, \log_b(d+1))$:
--   $$D_b(x) = d \iff \log_b d \le \{\log_b x\} < \log_b(d+1).$$
--
--   This is the observation behind the logarithmic form of the law: the probability of leading digit $d$ is the length of the interval $[\log_b d,\log_b(d+1))$ whenever $\{\log_b x\}$ is uniformly distributed.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Definition" ("x starts with the digit 1 if log 1 ≤ log x < log 2 ...").

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem leadingDigit_eq_iff_fract_logb (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : 0 < x)
    (d : ℕ) (hd1 : 1 ≤ d) (hdb : d < b) :
    leadingDigit b x = d ↔
      Real.logb b d ≤ Int.fract (Real.logb b x) ∧
        Int.fract (Real.logb b x) < Real.logb b (d + 1) := by sorry

end BenfordLaw
