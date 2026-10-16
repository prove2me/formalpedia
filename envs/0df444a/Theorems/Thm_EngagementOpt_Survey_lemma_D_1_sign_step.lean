-- Prove2me | Theorems.Thm_EngagementOpt_Survey_lemma_D_1_sign_step
-- name    : EngagementOpt.Survey.lemma_D_1_sign_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:52.430433+00:00
-- url     : https://prove2.me/theorems/e6735956-0dfb-482c-8b3c-937d8b757ccd
-- title:
--   Proof of Lemma D.1: sign of $(x+2)\ln(x+1)-2x$
-- statement:
--   The function $x\mapsto (x+2)\ln(x+1)-2x$ satisfies
--
--   1. $(x+2)\ln(x+1)-2x\ge0$ for every $x>0$;
--   2. $(x+2)\ln(x+1)-2x\le0$ for every $x\in(-1,0)$.
--
--   Since the derivative of $\varphi$ is $\bigl((x+2)\ln(x+1)-2x\bigr)/x^3$, this is the sign information that makes $\varphi$ increasing on $(-1,0)$ and on $(0,\infty)$ in the proof of Lemma D.1.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 41, proof of Lemma D.1

import Mathlib

namespace EngagementOpt.Survey

/-- arXiv:2202.11776v3, p. 41, proof of Lemma D.1: `(x + 2) ln(x + 1) - 2x` is weakly positive
for `x > 0` and weakly negative for `x ∈ (-1, 0)`. -/
theorem lemma_D_1_sign_step :
    (∀ x : ℝ, 0 < x → 0 ≤ (x + 2) * Real.log (x + 1) - 2 * x) ∧
    (∀ x : ℝ, -1 < x → x < 0 → (x + 2) * Real.log (x + 1) - 2 * x ≤ 0) := by sorry

end EngagementOpt.Survey
