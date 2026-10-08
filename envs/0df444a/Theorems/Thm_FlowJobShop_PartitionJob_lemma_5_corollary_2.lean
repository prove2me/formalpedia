-- Prove2me | Theorems.Thm_FlowJobShop_PartitionJob_lemma_5_corollary_2
-- name    : FlowJobShop.PartitionJob.lemma_5_corollary_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:01.488299+00:00
-- url     : https://prove2.me/theorems/b18ae22a-42b7-4c61-b3fc-f6bd2f48cba8
-- title:
--   Lemma 5 and Corollary 2 (pp. 43–44) — the Partition job shop JS has a schedule of finish time $\le 5T$, preemptive or not, iff a partition exists
-- statement:
--   Let $a_1, \dots, a_n$ be nonnegative integers and $T = \sum_{i=1}^n a_i$. Let $\mathrm{JS}$ be the job shop with two processors $P_1, P_2$ and $n+2$ jobs in which job $i \le n$ has tasks $(P_2, a_i), (P_1, a_i)$, job $n+1$ has tasks $(P_1, T/2), (P_2, T/2), (P_1, 3T)$, and job $n+2$ has tasks $(P_2, 3T), (P_1, T/2), (P_2, T/2)$. Then the following are equivalent:
--
--   1. $\mathrm{JS}$ has a preemptive schedule with finish time $\le 5T$;
--   2. $\mathrm{JS}$ has a non-preemptive schedule with finish time $\le 5T$;
--   3. $\{a_1, \dots, a_n\}$ has a partition, $\sum_{i \in u} a_i = T/2$ for some index set $u$.
--
--   $$
--   (1) \iff (3) \qquad\text{and}\qquad (2) \iff (3).
--   $$
--
--   The paper states these as Lemma 5, "Partition $\alpha$ preemptive JOFT", and Corollary 2, "Partition $\alpha$ nonpreemptive JOFT", and summarizes: finding optimal finish time preemptive schedules when $m = 2$ is NP-complete even when the job mix contains only two jobs with three nonzero tasks. Their proofs establish the two equivalences above for the constructed instance, which is what is formalized.
--
--   **Formalization Note** NP-completeness, the reduction's polynomial running time and Lemma 6 (JOFT is in NP) are not formalized. Schedules are finite sets of pieces (task, start, end) as in the paper's footnote 1, p. 40.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), pp. 43–44, Lemma 5 and Corollary 2

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionJob_Schedule
import Definitions.Def_FlowJobShop_PartitionJob_JS

namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

/-- Lemma 5 and Corollary 2 (Gonzalez–Sahni 1978, pp. 43–44): for every PARTITION instance `a`,
the two-processor job shop `JS(a)` (`n` jobs with two tasks, two jobs with three tasks) has a
preemptive schedule with finish time `≤ 5T` iff `a` has a partition, and has a non-preemptive
schedule with finish time `≤ 5T` iff `a` has a partition. -/
theorem lemma_5_corollary_2 {n : ℕ} (a : Fin n → ℕ) :
    ((∃ S : Schedule (JS a), S.IsPreemptive ∧ S.FinishedBy (5 * FlowJobShop.PartitionFlow.T a)) ↔ FlowJobShop.PartitionFlow.HasPartition a) ∧
    ((∃ S : Schedule (JS a), S.IsNonPreemptive ∧ S.FinishedBy (5 * FlowJobShop.PartitionFlow.T a)) ↔ FlowJobShop.PartitionFlow.HasPartition a) := by sorry

end FlowJobShop.PartitionJob
