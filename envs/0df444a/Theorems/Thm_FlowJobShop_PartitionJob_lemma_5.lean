-- Prove2me | Theorems.Thm_FlowJobShop_PartitionJob_lemma_5
-- name    : FlowJobShop.PartitionJob.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:32.539096+00:00
-- url     : https://prove2.me/theorems/a0a05cea-d866-4310-87fe-c8330acf2cee
-- title:
--   Lemma 5 — JS has a preemptive schedule with finish time $\le 5T$ iff $a$ has a partition
-- statement:
--   Let $a_1, \dots, a_n$ be nonnegative integers, $T = \sum_i a_i$, and let $\mathrm{JS}$ be the two-processor job shop with $n+2$ jobs built from them in the proof of Lemma 5. Then
--
--   $$
--   \exists\ \text{preemptive schedule } S \text{ of } \mathrm{JS} \text{ with } \mathrm{FT}(S) \le 5T \iff \{a_1, \dots, a_n\} \text{ has a partition.}
--   $$
--
--   The paper states Lemma 5 as "Partition $\alpha$ preemptive JOFT", i.e. PARTITION reduces in polynomial time to preemptive JOFT; its proof establishes the equivalence above for the instance it constructs, which is what is formalized. Together with Lemma 6 (JOFT is in NP) it shows that minimizing finish time for preemptive two-processor job shops is NP-complete.
--
--   **Formalization Note** The polynomial-time computability of the construction and the complexity-theoretic wording are not formalized.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 43, Lemma 5 (proof pp. 43–44)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionJob_Schedule
import Definitions.Def_FlowJobShop_PartitionJob_JS

namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

/-- Lemma 5 (Gonzalez–Sahni 1978, p. 43), in the form its proof establishes: the job shop `JS(a)`
has a preemptive schedule with finish time `≤ 5T` iff `a` has a partition. -/
theorem lemma_5 {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : Schedule (JS a), S.IsPreemptive ∧ S.FinishedBy (5 * FlowJobShop.PartitionFlow.T a)) ↔ FlowJobShop.PartitionFlow.HasPartition a := by sorry

end FlowJobShop.PartitionJob
