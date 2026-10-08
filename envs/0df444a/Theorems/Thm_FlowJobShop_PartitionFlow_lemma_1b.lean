-- Prove2me | Theorems.Thm_FlowJobShop_PartitionFlow_lemma_1b
-- name    : FlowJobShop.PartitionFlow.lemma_1b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:34:18.330776+00:00
-- url     : https://prove2.me/theorems/fba9f7b9-e055-4157-87cf-dfc6607926d0
-- title:
--   Lemma 1(b): if $S$ has no partition, every preemptive schedule of FS has finish time $> 2T$
-- statement:
--   Let $S=\{a_1,\dots,a_n\}$, $T=\sum_i a_i$ and FS be as in the proof of Lemma 1. If $S$ has no partition, then every preemptive schedule $S'$ of FS satisfies
--   $$\mathrm{FT}(S')>2T .$$
--
--   This is the hard direction of the reduction; together with Lemma 1(a) it shows that FS with threshold $2T$ answers the partition question for $S$, for preemptive and non-preemptive schedules alike.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 39, §1 Flow Shop, proof of Lemma 1, (b)

import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Lemma 1(b) (Gonzalez–Sahni 1978, p. 39): if `S = {a_1, …, a_n}` has no partition, then every
preemptive schedule of the flow shop FS built from it has finish time `> 2T`. -/
theorem lemma_1b {n : ℕ} (a : Fin n → ℕ) (h : ¬ HasPartition a) :
    ∀ S : PreemptiveSchedule (FS a), 2 * T a < S.finishTime := by sorry

end FlowJobShop.PartitionFlow
