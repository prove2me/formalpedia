-- Prove2me | Theorems.Thm_FlowJobShop_PartitionFlow_theorem_1
-- name    : FlowJobShop.PartitionFlow.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:34:34.836175+00:00
-- url     : https://prove2.me/theorems/3a3097d1-981c-4dbb-8204-c34cb09f8a4e
-- title:
--   Theorem 1: the three-machine flow shop FS, with at most two nonzero tasks per job, has a schedule of finish time $\le 2T$, preemptive or not, iff $S$ has a partition
-- statement:
--   Let $S=\{a_1,\dots,a_n\}$ be a multiset of nonnegative integers, $T=\sum_{i=1}^n a_i$, and FS the flow shop with $m=3$ processors and $n+2$ jobs built from $S$ in the proof of Lemma 1. Then
--
--   1. every job of FS has at most two nonzero tasks;
--   2. FS has a preemptive schedule with finish time $\le 2T$ if and only if $S$ has a partition;
--   3. FS has a non-preemptive schedule with finish time $\le 2T$ if and only if $S$ has a partition.
--
--   In symbols, with $\mathrm{FT}$ the finish time,
--   $$\big(\exists S'\ \text{preemptive},\ \mathrm{FT}(S')\le 2T\big)\iff \mathrm{PARTITION}(S)\iff\big(\exists S'\ \text{non-preemptive},\ \mathrm{FT}(S')\le 2T\big).$$
--
--   The paper states Theorem 1 as "FOFT with $m=3$ and no job having more than two nonzero tasks is NP-complete", proved by Lemma 1 (Partition reduces to preemptive FOFT), Lemma 2 (preemptive FOFT is in NP) and the remark that the same proof covers non-preemptive FOFT (Corollary 1). The formal statement is the mathematical content of the hardness half: the restriction to three processors and two nonzero tasks per job, and the equivalence for the constructed instance in both scheduling models. This makes the three-machine flow shop with two nonzero tasks per job the simplest flow-shop finish-time problem known to be NP-complete.
--
--   **Formalization Note** "NP-complete", polynomial-time reducibility and membership in NP (Lemma 2) are not formalized. $m=3$ is fixed by the type of FS.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 38, Theorem 1 (with Lemma 1, p. 38–39, and Corollary 1, pp. 39–40)

import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Theorem 1 (Gonzalez–Sahni 1978, p. 38), in the form its proof establishes: for every
PARTITION instance `S = {a_1, …, a_n}`, the three-processor flow shop FS built from it has at
most two nonzero tasks per job, and it has a preemptive schedule with finish time `≤ 2T` iff
`S` has a partition, and a non-preemptive schedule with finish time `≤ 2T` iff `S` has a
partition. -/
theorem theorem_1 {n : ℕ} (a : Fin n → ℕ) :
    (FS a).AtMostTwoNonzeroTasks ∧
      ((∃ S : PreemptiveSchedule (FS a), S.finishTime ≤ 2 * T a) ↔ HasPartition a) ∧
      ((∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime ≤ 2 * T a) ↔
        HasPartition a) := by sorry

end FlowJobShop.PartitionFlow
