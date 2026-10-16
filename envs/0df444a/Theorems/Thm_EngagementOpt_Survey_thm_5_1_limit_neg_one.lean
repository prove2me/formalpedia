-- Prove2me | Theorems.Thm_EngagementOpt_Survey_thm_5_1_limit_neg_one
-- name    : EngagementOpt.Survey.thm_5_1_limit_neg_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:03.288854+00:00
-- url     : https://prove2.me/theorems/90b091f3-9f2a-46c3-8bbf-0b6616ba3bd9
-- title:
--   Proof of Theorem 5.1, case $q<p$: $\lim_{x\to-1^+}\varphi(x)=0$
-- statement:
--   With $\varphi(x)=\dfrac{x+1}{x}\left(1-\dfrac{\ln(x+1)}{x}\right)$,
--
--   $$
--   \lim_{x\to-1^+}\varphi(x)=0 .
--   $$
--
--   When $q<p$, $x=\beta^t-1\to-1$ from above as $t\to\infty$, so the growth rate of $\mathbb E[T_q\mid T=t]$ tends to $0$; this gives part 3(b) of Theorem 5.1.
--
--   **Formalization Note** The limit is taken along the right neighbourhood of $-1$ (`𝓝[>] (-1)`), where $\ln(x+1)$ is the genuine logarithm.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 22, proof of Theorem 5.1, case 3

import Mathlib
import Definitions.Def_EngagementOpt_Survey_phi

namespace EngagementOpt.Survey

open Filter Topology

/-- arXiv:2202.11776v3, p. 22, proof of Theorem 5.1, case `q < p`:
`lim_{x → -1⁺} (x + 1)/x · (1 - ln(x + 1)/x) = 0`. -/
theorem thm_5_1_limit_neg_one : Tendsto phi (𝓝[>] (-1 : ℝ)) (𝓝 0) := by sorry

end EngagementOpt.Survey
