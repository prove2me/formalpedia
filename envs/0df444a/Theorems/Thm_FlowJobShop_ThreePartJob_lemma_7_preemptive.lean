-- Prove2me | Theorems.Thm_FlowJobShop_ThreePartJob_lemma_7_preemptive
-- name    : FlowJobShop.ThreePartJob.lemma_7_preemptive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:38:11.356082+00:00
-- url     : https://prove2.me/theorems/44d5d5b7-1185-43e1-bc8d-9e2369f2c9d0
-- title:
--   Lemma 7 — preemptive finish time 2tB iff 3-PARTITION is solvable
-- statement:
--   For every valid 3-PARTITION instance $C$ with $t$ groups of target sum $B$, construct the two-machine job shop $JS(C)$ of Lemma 7. Then
--
--   $$JS(C)\text{ has a preemptive schedule with }FT\le 2tB\quad\Longleftrightarrow\quad C\text{ has a 3-partition}.$$
--
--   This is the decision equivalence established inside the proof of Lemma 7. It is the mathematical reduction on which the paper's preemptive complexity claim rests.
--
--   **Formalization Note** The paper states this as “3-Partition $\alpha$ preemptive JOFT with $m=2$.” The formal theorem is the explicit equivalence for the constructed instance. It does not encode polynomial-time reduction or NP membership.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 44, Lemma 7 and its proof, https://doi.org/10.1287/opre.26.1.36

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- Lemma 7, p. 44: the constructed two-machine job shop admits a
preemptive schedule of finish time at most `2tB` exactly when the input
has a 3-partition. -/
theorem lemma_7_preemptive (C : ThreePartition) (hvalid : C.Valid) :
    (∃ S : PreemptiveSchedule (reductionInstance C),
      S.FinishesBy (threshold C)) ↔ C.HasSolution := by sorry

end FlowJobShop.ThreePartJob
