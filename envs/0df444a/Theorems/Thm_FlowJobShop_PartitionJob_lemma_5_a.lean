-- Prove2me | Theorems.Thm_FlowJobShop_PartitionJob_lemma_5_a
-- name    : FlowJobShop.PartitionJob.lemma_5_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:37.611383+00:00
-- url     : https://prove2.me/theorems/63291ad5-4c2b-48db-87b2-53e239110633
-- title:
--   Lemma 5(a) — if $a$ has a partition, JS has a non-preemptive schedule with finish time $5T$
-- statement:
--   Let $a_1, \dots, a_n$ be nonnegative integers, $T = \sum_i a_i$, and let $\mathrm{JS}$ be the two-processor job shop built from them in the proof of Lemma 5. If $\{a_1, \dots, a_n\}$ has a partition $u$, then $\mathrm{JS}$ has a non-preemptive schedule $S$ with
--
--   $$
--   \mathrm{FT}(S) \;=\; \max_i f_i(S) \;=\; 5T .
--   $$
--
--   This is the "partition implies schedule" half of the reduction; the paper exhibits the schedule in Figure 3, which is in particular a preemptive schedule.
--
--   **Formalization Note** "Finish time $5T$" is stated as: every job is finished by $5T$, and some job finishes exactly at $5T$.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 43, proof of Lemma 5, part (a) and Figure 3

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionJob_Schedule
import Definitions.Def_FlowJobShop_PartitionJob_JS

namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

/-- Lemma 5(a) (Gonzalez–Sahni 1978, p. 43): if the PARTITION instance `a` has a partition, the
job shop `JS(a)` has a (non-preemptive) schedule with finish time `5T`, i.e. every job is
finished by `5T` and some job finishes exactly at `5T`. -/
theorem lemma_5_a {n : ℕ} (a : Fin n → ℕ) (h : FlowJobShop.PartitionFlow.HasPartition a) :
    ∃ S : Schedule (JS a), S.IsNonPreemptive ∧ S.FinishedBy (5 * FlowJobShop.PartitionFlow.T a) ∧
      ∃ j : Fin (n + 2), S.jobFinish j = 5 * FlowJobShop.PartitionFlow.T a := by sorry

end FlowJobShop.PartitionJob
