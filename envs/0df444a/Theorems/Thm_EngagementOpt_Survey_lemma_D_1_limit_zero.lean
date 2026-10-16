-- Prove2me | Theorems.Thm_EngagementOpt_Survey_lemma_D_1_limit_zero
-- name    : EngagementOpt.Survey.lemma_D_1_limit_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:50.589131+00:00
-- url     : https://prove2.me/theorems/518ca0d8-c88d-4467-a2cb-8811fc200c20
-- title:
--   Proof of Lemma D.1, step 1: $\lim_{x\to0}\varphi(x)=\frac12$
-- statement:
--   With $\varphi(x)=\dfrac{x+1}{x}\left(1-\dfrac{\ln(x+1)}{x}\right)$,
--
--   $$
--   \lim_{x\to0,\ x\ne0}\varphi(x)=\frac12 .
--   $$
--
--   This is the first of the two facts from which the paper derives Lemma D.1: $\varphi$ has a removable singularity at $0$ with value $1/2$.
--
--   **Formalization Note** The limit is taken along the punctured neighbourhood of $0$ (`𝓝[≠] 0`), so the junk value of $\varphi$ at $0$ plays no role.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 40, proof of Lemma D.1, item 1

import Mathlib
import Definitions.Def_EngagementOpt_Survey_phi

namespace EngagementOpt.Survey

open Filter Topology

/-- arXiv:2202.11776v3, p. 40, proof of Lemma D.1, step 1:
`lim_{x → 0} (x + 1)/x · (1 - ln(x + 1)/x) = 1/2` (the limit over `x ≠ 0`). -/
theorem lemma_D_1_limit_zero : Tendsto phi (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2)) := by sorry

end EngagementOpt.Survey
