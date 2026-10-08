-- Prove2me | Theorems.Thm_FlowJobShop_PartitionJob_corollary_2
-- name    : FlowJobShop.PartitionJob.corollary_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:54.095303+00:00
-- url     : https://prove2.me/theorems/934e1aa5-b035-48ce-9aa7-6528df19cc46
-- title:
--   Corollary 2 — JS has a non-preemptive schedule with finish time $\le 5T$ iff $a$ has a partition
-- statement:
--   Let $a_1, \dots, a_n$ be nonnegative integers, $T = \sum_i a_i$, and let $\mathrm{JS}$ be the two-processor job shop with $n+2$ jobs built from them in the proof of Lemma 5. Then
--
--   $$
--   \exists\ \text{non-preemptive schedule } S \text{ of } \mathrm{JS} \text{ with } \mathrm{FT}(S) \le 5T \iff \{a_1, \dots, a_n\} \text{ has a partition.}
--   $$
--
--   The paper states Corollary 2 as "Partition $\alpha$ nonpreemptive JOFT", with proof "Same as above"; that proof establishes the equivalence above for the same instance, which is what is formalized.
--
--   **Formalization Note** A non-preemptive schedule is a preemptive one in which every task is processed in at most one piece. The complexity-theoretic wording is not formalized.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 44, Corollary 2

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionJob_Schedule
import Definitions.Def_FlowJobShop_PartitionJob_JS

namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

/-- Corollary 2 (Gonzalez–Sahni 1978, p. 44), in the form its proof establishes: the job shop
`JS(a)` has a non-preemptive schedule with finish time `≤ 5T` iff `a` has a partition. -/
theorem corollary_2 {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : Schedule (JS a), S.IsNonPreemptive ∧ S.FinishedBy (5 * FlowJobShop.PartitionFlow.T a)) ↔ FlowJobShop.PartitionFlow.HasPartition a := by sorry

end FlowJobShop.PartitionJob
