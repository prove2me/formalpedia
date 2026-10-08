-- Prove2me | Theorems.Thm_FlowJobShop_SPT_listSchedule_feasible
-- name    : FlowJobShop.SPT.listSchedule_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:38:33.063481+00:00
-- url     : https://prove2.me/theorems/2e2ca47b-4ac5-47da-b804-659d18cb954f
-- title:
--   SPT heuristic (pp. 46–47) — the list schedule is a feasible non-preemptive job-shop schedule
-- statement:
--   Let a job shop with $m$ processors and $n$ jobs be given, and let $\sigma$ be any order of the jobs. The list schedule $S_\sigma$ that processes the jobs $\sigma(0),\sigma(1),\dots$ in turn (each task starting as soon as its job's previous task and every task already placed on its processor have completed) is a feasible non-preemptive schedule of all jobs:
--
--   1. every task starts at a time $\ge 0$;
--   2. every task of a job other than its first starts no earlier than the completion of the preceding task of the same job;
--   3. two distinct tasks on the same processor do not overlap: one of them completes no later than the other starts.
--
--   In particular the SPT schedule is a feasible schedule, so Lemma 9 compares two feasible schedules.
--
--   **Formalization Note** The statement holds for every order $\sigma$, not only SPT orders. Feasibility uses the local `IsPaperFeasibleSchedule`, which excludes zero-time tasks from the machine-overlap condition. The paper assumes $m\ge1$.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), pp. 46–47 (the SPT heuristic, 'processing jobs in order of nondecreasing L_i')

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime
import Definitions.Def_FlowJobShop_SPT_ListSchedule

open JobShopLTAS.Core

namespace FlowJobShop.SPT

/-- The list schedule that processes the jobs in the order `σ` is a feasible non-preemptive
schedule of all jobs: starts are nonnegative, the tasks of a job are processed in order, and two
positive-time tasks on the same processor do not overlap. -/
theorem listSchedule_feasible {m n : ℕ} (inst : Instance m n) (hm : 0 < m)
    (σ : Fin n ≃ Fin n) :
    IsPaperFeasibleSchedule inst (listSchedule inst σ) := by sorry

end FlowJobShop.SPT
