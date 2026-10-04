-- Prove2me | Theorems.Thm_DelayedSWPT_Extended_piE_optimal
-- name    : DelayedSWPT.Extended.piE_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:09:17.808086+00:00
-- url     : https://prove2.me/theorems/aa8b71ae-126e-4bb5-bf4e-bf33fc92c378
-- title:
--   Lemma 2 — $\pi_E$ is an optimal schedule for the extended problem (E)
-- statement:
--   Let $\pi$ be the Delayed SWPT schedule of an instance (P), let (E) be the extended problem obtained by replacing the release dates by $r'_j = \max\{p_j, f(r_j)\}$ and adding a unit gap job $g_t$ (release date $f(r_j)$, weight $w_j/p_j$, where $j$ is the job Delayed SWPT selected but did not start at $t$) for every idle slot $[t, t+1)$ in which a job was available, and let $\pi_E$ be the schedule of (E) that runs the jobs of $J$ as in $\pi$ and each gap job $g_t$ in $[t, t+1)$. Then $\pi_E$ is optimal for (E):
--
--   $$\sum_{j\in J} w_j C_j(\pi_E) + \sum_{g\in G} w_g C_g(\pi_E) \;\le\; \sum_{j\in J} w_j C_j(\sigma) + \sum_{g\in G} w_g C_g(\sigma)$$
--
--   for every feasible nonpreemptive schedule $\sigma$ of (E).
--
--   This lemma says that Delayed SWPT is optimal once its idle time is charged to the gap jobs; it is the lower-bound side of the reduction in Lemma 3.
-- source:
--   Anderson and Potts, Online Scheduling of a Single Machine to Minimize Total Weighted Completion Time, Math. Oper. Res. 29(3) (2004), p. 690, Lemma 2

import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Lemma 2 of Anderson and Potts (2004), p. 690: `π_E` is an optimal schedule for the
extended problem (E), among all feasible nonpreemptive schedules of (E). -/
theorem piE_optimal {n : ℕ} (I : Instance n) :
    IsOptimal (rE I) (pE I) (wE I) (piE I) := by sorry

end DelayedSWPT.Extended
