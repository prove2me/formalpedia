-- Prove2me | Theorems.Thm_FlowJobShop_SPT_lemma_9
-- name    : FlowJobShop.SPT.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:41:06.454983+00:00
-- url     : https://prove2.me/theorems/4efa3a0f-5b90-4080-b726-7770d2d8984b
-- title:
--   Lemma 9 — the SPT schedule has mean flow time at most $m$ times the optimum, $\mathrm{MFT}(S)/\mathrm{MFT}(S^*)\le m$
-- statement:
--   Let a job shop with $m$ processors and $n$ jobs be given; job $i$ is a finite sequence of tasks, each on a prescribed processor with a processing time $\ge 0$, and $L_i$ is the sum of the task times of job $i$. Let $S$ be an SPT schedule: the list schedule that processes the jobs in an order $\sigma$ with $L_{\sigma(0)}\le\cdots\le L_{\sigma(n-1)}$ (ties broken arbitrarily), each task starting as soon as its job's previous task and every task already placed on its processor have completed. Then for every feasible non-preemptive schedule $\tau$,
--   $$
--   \mathrm{MFT}(S)\ \le\ m\cdot\mathrm{MFT}(\tau).
--   $$
--   In particular, for an optimal mean flow time schedule $S^*$, $\mathrm{MFT}(S)/\mathrm{MFT}(S^*)\le m$, which is Lemma 9 of Gonzalez and Sahni. Their Example 2 shows that the factor $m$ cannot be improved.
--
--   The paper states the lemma for "an $m$-processor, $n$-job flow (or job) shop problem"; the job shop contains the flow shop as the special case of $m$ tasks per job in processor order, stated separately in this mission.
--
--   **Formalization Note** The ratio is stated multiplied out, so a zero optimal mean flow time causes no division by zero. Comparing with every feasible schedule $\tau$ implies the comparison with an OMFT schedule and avoids assuming that one exists. Schedules are non-preemptive; the local feasibility predicate treats zero-time tasks as occupying no processor interval. The paper assumes $m\ge1$. Its remark "(it is assumed that $m<n$)" compares Lemma 9 with Lemma 8 and is not a hypothesis of Lemma 9.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 47, Lemma 9 (proof p. 47; SPT defined pp. 46–47)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime
import Definitions.Def_FlowJobShop_SPT_ListSchedule

open JobShopLTAS.Core

namespace FlowJobShop.SPT

/-- **Lemma 9** (Gonzalez–Sahni 1978, p. 47). In an `m`-processor, `n`-job job shop, the SPT
schedule (the list schedule in any order `σ` of nondecreasing total task time) has mean flow time
at most `m` times that of every feasible non-preemptive schedule `τ`, hence at most `m` times the
optimal mean flow time: `MFT(S) ≤ m · MFT(S*)`, the ratio bound `MFT(S)/MFT(S*) ≤ m` multiplied
out. -/
theorem lemma_9 {m n : ℕ} (inst : Instance m n) (hm : 0 < m)
    (σ : Fin n ≃ Fin n) (hσ : IsSPTOrder inst σ)
    (τ : inst.Op → ℝ) (hτ : IsPaperFeasibleSchedule inst τ) :
    meanFlowTime inst (listSchedule inst σ) ≤ (m : ℝ) * meanFlowTime inst τ := by sorry

end FlowJobShop.SPT
