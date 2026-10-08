-- Prove2me | Theorems.Thm_FlowJobShop_PartitionJob_lemma_5_b
-- name    : FlowJobShop.PartitionJob.lemma_5_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:01.325002+00:00
-- url     : https://prove2.me/theorems/846ab41f-09c8-451f-9453-13d560d668cc
-- title:
--   Lemma 5(b) — if $a$ has no partition, every preemptive schedule of JS has finish time $> 5T$
-- statement:
--   Let $a_1, \dots, a_n$ be nonnegative integers, $T = \sum_i a_i$, and let $\mathrm{JS}$ be the two-processor job shop built from them in the proof of Lemma 5. If $\{a_1, \dots, a_n\}$ has no partition, then every preemptive schedule $S$ of $\mathrm{JS}$ satisfies
--
--   $$
--   \mathrm{FT}(S) \;=\; \max_i f_i(S) \;>\; 5T .
--   $$
--
--   This is the "schedule implies partition" half of the reduction; since non-preemptive schedules are preemptive, it also covers them.
--
--   **Formalization Note** "$\mathrm{FT}(S) > 5T$" is stated as the existence of a job $j$ with $f_j(S) > 5T$.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), pp. 43–44, proof of Lemma 5, part (b)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionJob_Schedule
import Definitions.Def_FlowJobShop_PartitionJob_JS

namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

/-- Lemma 5(b) (Gonzalez–Sahni 1978, pp. 43–44): if the PARTITION instance `a` has no partition,
then every preemptive schedule of `JS(a)` has finish time `> 5T`: some job finishes after `5T`. -/
theorem lemma_5_b {n : ℕ} (a : Fin n → ℕ) (h : ¬ FlowJobShop.PartitionFlow.HasPartition a) (S : Schedule (JS a))
    (hS : S.IsPreemptive) : ∃ j : Fin (n + 2), 5 * FlowJobShop.PartitionFlow.T a < S.jobFinish j := by sorry

end FlowJobShop.PartitionJob
