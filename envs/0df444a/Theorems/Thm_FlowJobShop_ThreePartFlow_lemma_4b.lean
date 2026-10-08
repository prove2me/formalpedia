-- Prove2me | Theorems.Thm_FlowJobShop_ThreePartFlow_lemma_4b
-- name    : FlowJobShop.ThreePartFlow.lemma_4b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:37:03.682981+00:00
-- url     : https://prove2.me/theorems/06de0599-fc3c-4c06-8f60-05d7c24cc684
-- title:
--   Lemma 4(b) — without a 3-partition every preemptive schedule of FS has finish time > 2tB
-- statement:
--   Let $C=(a_1,\dots,a_s,B)$, $s=3t$, $t\ge 2$, be an instance of 3-Partition ($B>0$, $\sum_i a_i=tB$, $B/4<a_i<B/2$), and let $FS$ be the three-processor flow shop built from it in the proof of Lemma 4. If $C$ has no 3-partition, then every preemptive schedule $S$ of $FS$ satisfies
--   $$FT(S)>2tB .$$
--
--   This is the "only if" half of the reduction from 3-Partition to preemptive three-processor flow-shop scheduling.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), pp. 41–42, proof of Lemma 4, part (b)

import Mathlib
import Definitions.Def_FlowJobShop_ThreePartFlow_FlowShop
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_FlowJobShop_ThreePartFlow_Instance

open ResourceScheduling.Chain
open FlowJobShop.ThreePartFlow.FlowShop

namespace FlowJobShop.ThreePartFlow

/-- Lemma 4(b) (Gonzalez–Sahni 1978, proof of Lemma 4, pp. 41–42): if the 3-Partition instance
`C` (`t ≥ 2`) has no 3-partition, then every preemptive schedule of the flow shop `FS` built
from it has finish time `> 2tB`. -/
theorem lemma_4b (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t) (hno : ¬ C.HasSolution) :
    ∀ S : PreemptiveSchedule (FS C), tau C < S.finishTime := by sorry

end FlowJobShop.ThreePartFlow
