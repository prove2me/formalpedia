-- Prove2me | Theorems.Thm_DelayedSWPT_Model_dswpt_start_ge_p
-- name    : DelayedSWPT.Model.dswpt_start_ge_p
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:47:10.433224+00:00
-- url     : https://prove2.me/theorems/09bd5831-84e7-42fa-b64a-b964d4a14bc1
-- title:
--   Under Delayed SWPT no job $j$ starts before time $p_j$
-- statement:
--   Let $\pi$ be the Delayed SWPT schedule of an instance with integer release dates $r_j$, processing times $p_j \ge 1$ and positive weights $w_j$. Then every job starts no earlier than its own processing time:
--
--   $$\pi_j \ge p_j \qquad \text{for every job } j.$$
--
--   This is the defining feature of Delayed SWPT and the source of its factor 2: a job may be delayed, but never by more than its own length beyond the time it could otherwise run.
-- source:
--   Anderson and Potts, Online Scheduling of a Single Machine to Minimize Total Weighted Completion Time, Math. Oper. Res. 29(3) (2004), p. 689, §2

import Mathlib
import Definitions.Def_DelayedSWPT_Model_dswpt

namespace DelayedSWPT.Model

/-- Anderson and Potts (2004), §2, p. 689: under Delayed SWPT no job `j` starts before time
`p_j`. -/
theorem dswpt_start_ge_p {n : ℕ} (I : Instance n) (j : Fin n) : I.p j ≤ dswpt I j := by sorry

end DelayedSWPT.Model
