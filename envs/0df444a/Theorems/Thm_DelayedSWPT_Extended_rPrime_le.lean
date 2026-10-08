-- Prove2me | Theorems.Thm_DelayedSWPT_Extended_rPrime_le
-- name    : DelayedSWPT.Extended.rPrime_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:08:36.850611+00:00
-- url     : https://prove2.me/theorems/a691aabe-7f5c-453b-a73e-da1bd1912291
-- title:
--   The transformed release dates satisfy $r'_j \le \max\{2r_j, p_j\}$
-- statement:
--   Let $\pi$ be the Delayed SWPT schedule of an instance (P), let $f(t)$ be the first time at or after $t$ at which the machine is available in $\pi$, and let $r'_j = \max\{p_j, f(r_j)\}$ be the release dates of the transformed problem (P′). Then for every job $j$,
--
--   $$r'_j \le \max\{2r_j,\, p_j\}.$$
--
--   This bound is what makes the nongap jobs of an optimal schedule of the doubled problem (2P) release-feasible in the extended problem (E).
-- source:
--   Anderson and Potts, Online Scheduling of a Single Machine to Minimize Total Weighted Completion Time, Math. Oper. Res. 29(3) (2004), p. 689, §3.2

import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Anderson and Potts (2004), §3.2, p. 689: the transformed release dates satisfy
`r′ⱼ ≤ max {2rⱼ, pⱼ}`. -/
theorem rPrime_le {n : ℕ} (I : Instance n) (j : Fin n) :
    rPrime I j ≤ max (2 * I.r j) (I.p j) := by sorry

end DelayedSWPT.Extended
