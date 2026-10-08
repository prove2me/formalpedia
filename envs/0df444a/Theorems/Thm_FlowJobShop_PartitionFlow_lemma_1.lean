-- Prove2me | Theorems.Thm_FlowJobShop_PartitionFlow_lemma_1
-- name    : FlowJobShop.PartitionFlow.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:34:15.393679+00:00
-- url     : https://prove2.me/theorems/edb7ad1e-2636-4d25-9399-8c5f05808984
-- title:
--   Lemma 1: FS has a preemptive schedule with finish time $\le 2T$ iff $S$ has a partition
-- statement:
--   Let $S=\{a_1,\dots,a_n\}$ be a multiset of nonnegative integers, $T=\sum_i a_i$, and FS the three-processor flow shop with at most two nonzero tasks per job built from $S$ in the proof of Lemma 1. Then
--   $$\exists\ \text{preemptive schedule } S' \text{ of FS with } \mathrm{FT}(S')\le 2T\iff S \text{ has a partition}.$$
--
--   The paper states Lemma 1 as "Partition $\alpha$ preemptive FOFT with $m=3$ and at most two nonzero tasks per job"; its proof establishes the equivalence above for the instance FS and threshold $\tau=2T$, which is what is formalized. Since FS is clearly computable from $S$ in polynomial time, this equivalence is the mathematical content of the reduction.
--
--   **Formalization Note** Polynomial-time reducibility ("$\alpha$") is not formalized; only the equivalence for the constructed instance is.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 38, Lemma 1 (proof p. 39)

import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Lemma 1 (Gonzalez–Sahni 1978, p. 38; proof p. 39), in the form its proof establishes: the
three-processor flow shop FS built from `S = {a_1, …, a_n}` has a preemptive schedule with
finish time `≤ 2T` iff `S` has a partition. -/
theorem lemma_1 {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : PreemptiveSchedule (FS a), S.finishTime ≤ 2 * T a) ↔ HasPartition a := by sorry

end FlowJobShop.PartitionFlow
