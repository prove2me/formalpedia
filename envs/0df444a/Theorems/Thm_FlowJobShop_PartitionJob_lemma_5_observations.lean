-- Prove2me | Theorems.Thm_FlowJobShop_PartitionJob_lemma_5_observations
-- name    : FlowJobShop.PartitionJob.lemma_5_observations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:03.338892+00:00
-- url     : https://prove2.me/theorems/ca3579b4-ba43-4fe4-a34e-db4cd569d0fe
-- title:
--   Lemma 5, observations (i)–(ii) — where jobs $n+1$, $n+2$ must run in a schedule of finish time $\le 5T$
-- statement:
--   Let $\mathrm{JS}$ be the job shop built from $a_1, \dots, a_n$ in the proof of Lemma 5, with $T = \sum_i a_i$, and let $S$ be a preemptive schedule of $\mathrm{JS}$ with finish time at most $5T$. Then:
--
--   1. on processor 2, task $t_{2,n+1,2}$ is completed by time $2T$ and task $t_{2,n+2,1}$ by time $4T$;
--   2. on processor 1, no part of task $t_{1,n+1,3}$ is processed before time $T$, and no part of task $t_{1,n+2,2}$ before time $3T$.
--
--   These observations fix where the two long tasks of length $3T$ can be processed and are the first step of the proof of Lemma 5(b).
--
--   **Formalization Note** Job $n+1$ of the paper is job `n` (0-based) and job $n+2$ is job `n + 1`; the paper's task $j$ is task $j-1$. Part (i) bounds the completion times `S.completed n 2` and `S.completed (n+1) 1`; part (ii) bounds the start of every piece of the two tasks. The paper's parenthetical consequence ("before $4T$ only $T/2$ units are free for jobs $1, \dots, n$") is not part of this statement.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 44, proof of Lemma 5(b), observations (i) and (ii)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionJob_Schedule
import Definitions.Def_FlowJobShop_PartitionJob_JS

namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

/-- Observations (i)–(ii) in the proof of Lemma 5(b) (Gonzalez–Sahni 1978, p. 44). In every
preemptive schedule of `JS(a)` with finish time `≤ 5T`:
(i) on processor 2, task `t_{2,n+1,2}` (0-based task 1 of job `n`) is completed by `2T` and task
`t_{2,n+2,1}` (0-based task 0 of job `n+1`) by `4T`;
(ii) on processor 1, no piece of `t_{1,n+1,3}` (0-based task 2 of job `n`) starts before `T`, and
no piece of `t_{1,n+2,2}` (0-based task 1 of job `n+1`) starts before `3T`. -/
theorem lemma_5_observations {n : ℕ} (a : Fin n → ℕ) (S : Schedule (JS a))
    (hS : S.IsPreemptive) (hFT : S.FinishedBy (5 * FlowJobShop.PartitionFlow.T a)) :
    S.completed (⟨n, by omega⟩ : Fin (n + 2)) 2 ≤ 2 * FlowJobShop.PartitionFlow.T a ∧
    S.completed (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 ≤ 4 * FlowJobShop.PartitionFlow.T a ∧
    (∀ q ∈ S.pieces, q.1.1.val = n → q.1.2.val = 2 → FlowJobShop.PartitionFlow.T a ≤ q.2.1) ∧
    (∀ q ∈ S.pieces, q.1.1.val = n + 1 → q.1.2.val = 1 → 3 * FlowJobShop.PartitionFlow.T a ≤ q.2.1) := by sorry

end FlowJobShop.PartitionJob
