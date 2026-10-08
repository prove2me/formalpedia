-- Prove2me | Theorems.Thm_FlowJobShop_ThreePartFlow_lemma_4b_first_step
-- name    : FlowJobShop.ThreePartFlow.lemma_4b_first_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:36:46.054053+00:00
-- url     : https://prove2.me/theorems/2ddedb6a-cbf0-48c5-a112-f1c30af38893
-- title:
--   Proof of Lemma 4(b) — exactly B units of jobs 1, …, s complete on P₁ by time 2B
-- statement:
--   Let $C=(a_1,\dots,a_s,B)$, $s=3t$, $t\ge 2$, be an instance of 3-Partition, and let $FS$ be the flow shop built from it in the proof of Lemma 4. Let $S$ be any preemptive schedule of $FS$ with $FT(S)\le 2tB$. Then the jobs among $1,\dots,s$ whose task on $P_1$ is completed by time $2B$ have first-processor times adding up to exactly $B$:
--   $$\sum_{\substack{1\le i\le s\\ c_{1,i}(S)\le 2B}} t_{1,i} \;=\; B,$$
--   where $c_{1,i}(S)$ is the completion time of the task of job $i$ on $P_1$.
--
--   This is the first step of the proof of Lemma 4(b); the paper then repeats the argument on $[2B,4B]$, $[4B,6B]$, … to extract a 3-partition.
--
--   **Formalization Note** The paper's phrase "exactly $B$ units of the processing required for jobs $1,\dots,s$ must be scheduled to complete on $P_1$ by time $2B$" is read as the sum of $t_{1,i}=a_i$ over the jobs $i\le s$ whose $P_1$ task has completed by time $2B$. The statement does not assume that $C$ lacks a 3-partition.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), pp. 41–42, proof of Lemma 4, part (b), first paragraph

import Mathlib
import Definitions.Def_FlowJobShop_ThreePartFlow_FlowShop
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_FlowJobShop_ThreePartFlow_Instance

open ResourceScheduling.Chain
open FlowJobShop.ThreePartFlow.FlowShop

namespace FlowJobShop.ThreePartFlow

/-- First step of Lemma 4(b) (Gonzalez–Sahni 1978, proof of Lemma 4, pp. 41–42): in every
preemptive schedule of `FS` with finish time `≤ 2tB`, the jobs among `1, …, s` whose task on
`P_1` is completed by time `2B` have `P_1` task times summing to exactly `B`. -/
theorem lemma_4b_first_step (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t)
    (S : PreemptiveSchedule (FS C)) (hS : S.finishTime ≤ tau C) :
    ∑ i ∈ Finset.univ.filter
        (fun i : Fin (3 * C.t) => S.taskCompletion 0 (FSJob.elem i) ≤ 2 * (C.b : ℝ)),
      (FS C).t 0 (FSJob.elem i) = (C.b : ℝ) := by sorry

end FlowJobShop.ThreePartFlow
