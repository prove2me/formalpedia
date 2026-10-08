-- Prove2me | Theorems.Thm_FlowJobShop_PartitionFlow_lemma_1a
-- name    : FlowJobShop.PartitionFlow.lemma_1a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:33:58.744774+00:00
-- url     : https://prove2.me/theorems/5bbf6972-51a4-4913-9a9b-37a48f295faa
-- title:
--   Lemma 1(a): a partition of $S$ gives a non-preemptive schedule of FS with finish time $2T$
-- statement:
--   Let $S=\{a_1,\dots,a_n\}$ be a multiset of nonnegative integers, $T=\sum_i a_i$, and FS the three-processor flow shop built from $S$ in the proof of Lemma 1 (jobs $1,\dots,n$ with times $(a_i,0,a_i)$, job $n+1$ with times $(T/2,T,0)$, job $n+2$ with times $(0,T,T/2)$). If $S$ has a partition, then FS has a non-preemptive schedule $S'$ with
--   $$\mathrm{FT}(S')=2T .$$
--
--   This is the easy direction of the reduction: the schedule of Figure 1 packs the three processors without idle time on $P_2$.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 39, §1 Flow Shop, proof of Lemma 1, (a) and Figure 1

import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Lemma 1(a) (Gonzalez–Sahni 1978, p. 39): if `S = {a_1, …, a_n}` has a partition, then the
flow shop FS built from it has a non-preemptive schedule with finish time `2T`. -/
theorem lemma_1a {n : ℕ} (a : Fin n → ℕ) (h : HasPartition a) :
    ∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime = 2 * T a := by sorry

end FlowJobShop.PartitionFlow
