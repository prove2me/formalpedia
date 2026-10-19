-- Prove2me | Theorems.Thm_EngagementOpt_Survey_eq_9_p_eq_q
-- name    : EngagementOpt.Survey.eq_9_p_eq_q
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:21.838998+00:00
-- url     : https://prove2.me/theorems/3bad12a8-b01f-4641-8319-bd3cd7b79045
-- title:
--   (9) with $p=q$: $\mathbb E[T_q\mid T_q+T_p=t+1]=\frac{t+1}{2}$
-- statement:
--   Let $0<q<1$ and let $T_q,T_p$ be independent with the same law $\mathrm{Geom}(1-q)$ on $\{1,2,\dots\}$ (that is, $p=q$). Then for every session length $t\ge1$,
--
--   $$
--   \mathbb E[T_q\mid T_q+T_p=t+1]=\frac{t+1}{2},
--   $$
--
--   where the conditional mean is defined by (9).
--
--   When the two phases have the same law, every split of the session is equally likely, so the span is on average half of $t+1$. This is the case $p=q$ of (10) and of Theorem 5.1(1).
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 20, sentence after (9)

import Mathlib
import Definitions.Def_EngagementOpt_Survey_condMeanTq

namespace EngagementOpt.Survey

/-- arXiv:2202.11776v3, p. 20, (9) for `p = q`: if `p = q ∈ (0, 1)`, then
`E[T_q | T_q + T_p = t + 1] = (t + 1)/2` for every session length `t ≥ 1`. -/
theorem eq_9_p_eq_q (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (t : ℕ) (ht : 1 ≤ t) :
    condMeanTq q q t = ((t : ℝ) + 1) / 2 := by sorry

end EngagementOpt.Survey
