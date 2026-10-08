-- Prove2me | Theorems.Thm_DelayedSWPT_Extended_piE_feasible
-- name    : DelayedSWPT.Extended.piE_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:08:51.276193+00:00
-- url     : https://prove2.me/theorems/bcef6b18-18da-4822-bdbf-9e25fbd68da5
-- title:
--   The schedule $\pi_E$ is feasible for the extended problem (E)
-- statement:
--   Let $\pi$ be the Delayed SWPT schedule of an instance (P), and let $\pi_E$ be the schedule of the extended problem (E) that starts each original job $j$ at $\pi_j$ and each gap job $g_t$ at its gap time $t$. Then $\pi_E$ is a feasible nonpreemptive schedule of (E): every job of $J \cup G$ starts no earlier than its release date in (E), and no two jobs overlap.
--
--   The optimality of $\pi_E$ for (E) is then a statement about a feasible schedule.
-- source:
--   Anderson and Potts, Online Scheduling of a Single Machine to Minimize Total Weighted Completion Time, Math. Oper. Res. 29(3) (2004), p. 690, §3.2

import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Anderson and Potts (2004), §3.2, p. 690: the schedule `π_E` is feasible for the extended
problem (E). -/
theorem piE_feasible {n : ℕ} (I : Instance n) : IsFeasible (rE I) (pE I) (piE I) := by sorry

end DelayedSWPT.Extended
