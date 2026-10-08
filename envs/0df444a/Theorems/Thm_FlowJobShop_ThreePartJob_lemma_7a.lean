-- Prove2me | Theorems.Thm_FlowJobShop_ThreePartJob_lemma_7a
-- name    : FlowJobShop.ThreePartJob.lemma_7a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:37:51.868078+00:00
-- url     : https://prove2.me/theorems/0b12250e-8703-4045-adaf-b45f925c8463
-- title:
--   Lemma 7(a) — a 3-partition gives a non-preemptive schedule by 2tB
-- statement:
--   Let $C=(a_1,\ldots,a_{3t},B)$ be a valid 3-PARTITION instance, and let $JS(C)$ be the two-machine job shop constructed in the proof of Lemma 7. If $C$ has a partition into $t$ three-element sets, each summing to $B$, then $JS(C)$ has a feasible non-preemptive schedule with finish time at most $2tB$:
--
--   $$C\text{ has a 3-partition}\quad\Longrightarrow\quad\exists S\text{ non-preemptive for }JS(C),\;FT(S)\le 2tB.$$
--
--   This is the constructive direction of the reduction and supplies the same direction for preemptive schedules.
--
--   **Formalization Note** The theorem asserts existence of start times satisfying the published job-shop feasibility predicate; the valid-input hypothesis includes the paper's bounds $B/4<a_i<B/2$.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), pp. 44–45, proof of Lemma 7(a), Figure 4, https://doi.org/10.1287/opre.26.1.36

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- Lemma 7(a), pp. 44–45: a 3-partition produces a nonpreemptive
schedule of the constructed job shop within `2tB`. -/
theorem lemma_7a (C : ThreePartition) (hvalid : C.Valid) (hsol : C.HasSolution) :
    ∃ s : (reductionInstance C).Op → ℝ,
      NonpreemptiveFinishesBy (reductionInstance C) s (threshold C) := by sorry

end FlowJobShop.ThreePartJob
