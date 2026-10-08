-- Prove2me | Theorems.Thm_FlowJobShop_ThreePartJob_lemma_7b
-- name    : FlowJobShop.ThreePartJob.lemma_7b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:38:06.697385+00:00
-- url     : https://prove2.me/theorems/7487b6e9-2759-4114-a153-7129b238828a
-- title:
--   Lemma 7(b) — absent a 3-partition, every preemptive schedule exceeds 2tB
-- statement:
--   Let $C$ be a valid 3-PARTITION input with no solution. Every feasible preemptive schedule $S$ of the constructed job shop $JS(C)$ has a processing piece ending strictly after the threshold $2tB$:
--
--   $$C\text{ has no 3-partition}\quad\Longrightarrow\quad FT(S)>2tB\quad\text{for every preemptive }S.$$
--
--   This is the converse direction of Lemma 7's reduction and rules out all non-preemptive schedules at the threshold as well.
--
--   **Formalization Note** Finish time above the threshold is stated by an explicit late piece. The finite schedule makes this equivalent to the paper's strict finish-time inequality, including the empty-piece corner case.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 45, proof of Lemma 7(b), https://doi.org/10.1287/opre.26.1.36

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- Lemma 7(b), p. 45: without a 3-partition, every preemptive
schedule of the constructed job shop finishes strictly after `2tB`. -/
theorem lemma_7b (C : ThreePartition) (hvalid : C.Valid) (hno : ¬ C.HasSolution) :
    ∀ S : PreemptiveSchedule (reductionInstance C),
      ∃ u : Fin S.pieceCount, threshold C < S.finish u := by sorry

end FlowJobShop.ThreePartJob
