-- Prove2me | Theorems.Thm_BenfordLaw_benfordProb_sum_eq_one
-- name    : BenfordLaw.benfordProb_sum_eq_one
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:25.671307+00:00
-- url     : https://prove2.me/theorems/98594153-5251-4019-90e0-9eddbb02c4ef
-- title:
--   Benford probabilities sum to $1$ in every base $b \ge 2$
-- statement:
--   Let $b \ge 2$ be an integer base and $P_b(d) = \log_b\!\left(1+\frac1d\right)$. Then the Benford probabilities of the digits $1,\dots,b-1$ form a probability distribution:
--   $$\sum_{d=1}^{b-1} \log_b\!\left(1+\frac1d\right) = 1 .$$
--
--   This is the normalization that makes the first-digit law a genuine probability law in every base.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, sections "Definition" and "In other bases" (formula $P(d)=\log_b(d+1)-\log_b d$).

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem benfordProb_sum_eq_one (b : ℕ) (hb : 2 ≤ b) :
    ∑ d ∈ Finset.Icc 1 (b - 1), benfordProb b d = 1 := by sorry

end BenfordLaw
