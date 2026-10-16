-- Prove2me | Theorems.Thm_EngagementOpt_Survey_thm_5_1_limit_atTop
-- name    : EngagementOpt.Survey.thm_5_1_limit_atTop
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:02.327061+00:00
-- url     : https://prove2.me/theorems/42349899-8a5f-4ecc-a539-ec1dff7ac2f7
-- title:
--   Proof of Theorem 5.1, case $q>p$: $\lim_{x\to\infty}\varphi(x)=1$
-- statement:
--   With $\varphi(x)=\dfrac{x+1}{x}\left(1-\dfrac{\ln(x+1)}{x}\right)$,
--
--   $$
--   \lim_{x\to\infty}\varphi(x)=1 .
--   $$
--
--   When $q>p$, $x=\beta^t-1\to\infty$ as $t\to\infty$, so the growth rate of $\mathbb E[T_q\mid T=t]$ tends to $1$; this gives part 2(b) of Theorem 5.1 when $\bar v>W$.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 22, proof of Theorem 5.1, case 2

import Mathlib
import Definitions.Def_EngagementOpt_Survey_phi

namespace EngagementOpt.Survey

open Filter Topology

/-- arXiv:2202.11776v3, p. 22, proof of Theorem 5.1, case `q > p`:
`lim_{x → ∞} (x + 1)/x · (1 - ln(x + 1)/x) = 1`. -/
theorem thm_5_1_limit_atTop : Tendsto phi atTop (𝓝 1) := by sorry

end EngagementOpt.Survey
