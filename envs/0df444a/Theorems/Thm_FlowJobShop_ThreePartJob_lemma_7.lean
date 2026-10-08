-- Prove2me | Theorems.Thm_FlowJobShop_ThreePartJob_lemma_7
-- name    : FlowJobShop.ThreePartJob.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:38:30.454552+00:00
-- url     : https://prove2.me/theorems/3f0f27f1-6185-4569-a40e-4291e650bc39
-- title:
--   Lemma 7 — the 3-PARTITION job shop meets 2tB, preemptively or not, iff a 3-partition exists
-- statement:
--   Let $C=(a_1,\ldots,a_{3t},B)$ be a valid 3-PARTITION instance: $B>0$, the numbers sum to $tB$, and $B/4<a_i<B/2$ for every $i$. Build the two-machine job shop $JS(C)$ of Lemma 7. The following two equivalences hold:
--
--   $$\begin{aligned}
--   JS(C)\text{ has a preemptive schedule with }FT\le 2tB
--     &\Longleftrightarrow C\text{ has a 3-partition},\\
--   JS(C)\text{ has a non-preemptive schedule with }FT\le 2tB
--     &\Longleftrightarrow C\text{ has a 3-partition}.
--   \end{aligned}$$
--
--   The preemptive equivalence is Lemma 7's stated reduction. Its proof also constructs a non-preemptive schedule when the partition exists and excludes every preemptive schedule when it does not, giving the second equivalence.
--
--   **Formalization Note** The paper phrases the result as “3-Partition $\alpha$ preemptive JOFT with $m=2$” and says this strengthens NP-completeness for both schedule types under the sum-of-task-lengths complexity measure. This theorem formalizes the proof's decision equivalences, not the reduction's computational complexity or the separate NP-membership result of Lemma 6. The empty-group case $t=0$ is included.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), pp. 44–45, Lemma 7 and parts (a)–(b), https://doi.org/10.1287/opre.26.1.36

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- Lemma 7, p. 44, with the nonpreemptive form established by its
part (a) and the inclusion of nonpreemptive schedules among preemptive
ones. The mathematical content is the reduction equivalence. -/
theorem lemma_7 (C : ThreePartition) (hvalid : C.Valid) :
    ((∃ S : PreemptiveSchedule (reductionInstance C),
      S.FinishesBy (threshold C)) ↔ C.HasSolution) ∧
    ((∃ s : (reductionInstance C).Op → ℝ,
      NonpreemptiveFinishesBy (reductionInstance C) s (threshold C)) ↔
        C.HasSolution) := by sorry

end FlowJobShop.ThreePartJob
