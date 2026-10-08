-- Prove2me | Theorems.Thm_FlowJobShop_PartitionFlow_corollary_1
-- name    : FlowJobShop.PartitionFlow.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:34:25.949458+00:00
-- url     : https://prove2.me/theorems/70d368b7-e0b6-49e9-b3d5-9fe7fabf3d54
-- title:
--   Corollary 1: FS has a non-preemptive schedule with finish time $\le 2T$ iff $S$ has a partition
-- statement:
--   Let $S=\{a_1,\dots,a_n\}$, $T=\sum_i a_i$ and FS be as in the proof of Lemma 1. Then
--   $$\exists\ \text{non-preemptive schedule } S' \text{ of FS with } \mathrm{FT}(S')\le 2T\iff S \text{ has a partition}.$$
--
--   The paper states Corollary 1 as "Partition $\alpha$ non-preemptive FOFT with $m=3$ and at most two nonzero tasks per job"; its proof says that the construction of Lemma 1 yields a flow shop with a non-preemptive schedule of finish time $\tau=2T$ iff $S$ has a partition. That equivalence, with "finish time $\le\tau$" as in the definition of FOFT, is what is formalized.
--
--   **Formalization Note** A non-preemptive schedule is a schedule with at most one piece per task. Polynomial-time reducibility is not formalized.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 39, Corollary 1 (proof pp. 39–40)

import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Corollary 1 (Gonzalez–Sahni 1978, pp. 39–40), in the form its proof establishes: the flow
shop FS of Lemma 1 has a non-preemptive schedule with finish time `≤ τ = 2T` iff
`S = {a_1, …, a_n}` has a partition. -/
theorem corollary_1 {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime ≤ 2 * T a) ↔
      HasPartition a := by sorry

end FlowJobShop.PartitionFlow
