-- Prove2me | Theorems.Thm_FlowJobShop_ThreePartFlow_lemma_4a
-- name    : FlowJobShop.ThreePartFlow.lemma_4a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:36:25.813147+00:00
-- url     : https://prove2.me/theorems/6ed0a2bf-2857-4312-bbf9-7acb7ebb2119
-- title:
--   Lemma 4(a) — a 3-partition gives a non-preemptive schedule of FS with finish time ≤ 2tB
-- statement:
--   Let $C=(a_1,\dots,a_s,B)$, $s=3t$, $t\ge 2$, be an instance of 3-Partition (so $B>0$, $\sum_i a_i=tB$ and $B/4<a_i<B/2$), and let $FS$ be the three-processor flow shop built from $C$ in the proof of Lemma 4. If $C$ has a 3-partition, that is, $\{1,\dots,s\}$ splits into disjoint sets $L_1,\dots,L_t$ with $|L_i|=3$ and $\sum_{j\in L_i}a_j=B$, then $FS$ has a non-preemptive schedule $S$ with
--   $$FT(S)\le 2tB .$$
--
--   This is the "if" half of the reduction from 3-Partition; the paper exhibits the schedule in its Figure 2.
--
--   **Formalization Note** A non-preemptive schedule is a preemptive schedule in which every task is processed in at most one piece; in particular it is itself a preemptive schedule.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 41, proof of Lemma 4, part (a), and Figure 2 (p. 42)

import Mathlib
import Definitions.Def_FlowJobShop_ThreePartFlow_FlowShop
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_FlowJobShop_ThreePartFlow_Instance

open ResourceScheduling.Chain
open FlowJobShop.ThreePartFlow.FlowShop

namespace FlowJobShop.ThreePartFlow

/-- Lemma 4(a) (Gonzalez–Sahni 1978, proof of Lemma 4, p. 41): if the 3-Partition instance
`C = (a_1, …, a_s, B)`, `s = 3t`, `t ≥ 2`, has a solution, then the flow shop `FS` built from
it has a non-preemptive schedule with finish time `≤ 2tB`. -/
theorem lemma_4a (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t) (hsol : C.HasSolution) :
    ∃ S : PreemptiveSchedule (FS C), S.IsNonPreemptive ∧ S.finishTime ≤ tau C := by sorry

end FlowJobShop.ThreePartFlow
