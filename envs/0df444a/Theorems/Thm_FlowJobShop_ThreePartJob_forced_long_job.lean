-- Prove2me | Theorems.Thm_FlowJobShop_ThreePartJob_forced_long_job
-- name    : FlowJobShop.ThreePartJob.forced_long_job
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:37:56.875357+00:00
-- url     : https://prove2.me/theorems/dc9e1b49-8596-496f-b43e-3a6fe1723a4b
-- title:
--   Lemma 7(b), first step — the long job occupies its alternating B-length slots
-- statement:
--   Let $C$ be a valid 3-PARTITION input and $S$ a feasible preemptive schedule of $JS(C)$ finishing by $2tB$. Number the operations of the final job from $i=0$ to $2t-1$. Every processing piece of its operation $i$ lies in the interval
--
--   $$[iB,(i+1)B].$$
--
--   Thus the final job has the timing shown in Figure 4. Together with the operation's total length $B$ and machine disjointness, the interval constraint expresses that its allotted slot is filled. It is an intermediate restriction on any schedule that meets the threshold.
--
--   **Formalization Note** A contiguous operation may be represented by adjacent pieces in the finite-piece model; the theorem constrains their occupied interval rather than demanding a particular piece count.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 45, proof of Lemma 7(b), sentence beginning 'Job s+1 has to be scheduled', https://doi.org/10.1287/opre.26.1.36

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- Proof of Lemma 7(b), p. 45: if the schedule ends by `2tB`, every
piece of operation `i` of the long job lies in its allotted interval
`[iB,(i+1)B]`. Total work and disjointness ensure the interval is filled. -/
theorem forced_long_job (C : ThreePartition) (hvalid : C.Valid)
    (S : PreemptiveSchedule (reductionInstance C))
    (hfinish : S.FinishesBy (threshold C)) :
    ∀ u : Fin S.pieceCount, (S.op u).1.val = 3 * C.t →
      ((S.op u).2.val : ℝ) * C.b ≤ S.start u ∧
        S.finish u ≤ (((S.op u).2.val + 1 : ℕ) : ℝ) * C.b := by sorry

end FlowJobShop.ThreePartJob
