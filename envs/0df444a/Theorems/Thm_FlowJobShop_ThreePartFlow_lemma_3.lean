-- Prove2me | Theorems.Thm_FlowJobShop_ThreePartFlow_lemma_3
-- name    : FlowJobShop.ThreePartFlow.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:16:54.458681+00:00
-- url     : https://prove2.me/theorems/92d3beb1-eafb-4403-965d-c99300bbf354
-- title:
--   Lemma 3 — a preemptive flow-shop schedule needs no preemptions on the first and last processors
-- statement:
--   Let $F$ be a flow shop with $m\ge 1$ processors and finitely many jobs, and let $S$ be any preemptive schedule of $F$. Then there is a preemptive schedule $S'$ of $F$ such that
--
--   1. no task on processor $P_1$ is preempted in $S'$,
--   2. no task on processor $P_m$ is preempted in $S'$, and
--   $$FT(S')=FT(S).$$
--
--   The lemma is used in the proof of Lemma 4(b): in a schedule of the 3-Partition flow shop one may assume the first-processor tasks are processed without interruption.
--
--   **Formalization Note** "No preemptions on $P_j$" means that every task on $P_j$ is processed in at most one piece. When $m=1$ the two conditions concern the same processor. The paper's conclusion $FT(S')=FT(S)$ is stated as an equality, as on the page.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 40, Lemma 3 (proof pp. 40–41)

import Mathlib
import Definitions.Def_FlowJobShop_ThreePartFlow_FlowShop

open FlowJobShop.ThreePartFlow.FlowShop

namespace FlowJobShop.ThreePartFlow

/-- Lemma 3 (Gonzalez–Sahni 1978, p. 40): any preemptive schedule `S` for a flow shop with
`m ≥ 1` processors can be transformed to a schedule `S'` in which there are no preemptions on
processors `P_1` (index `0`) and `P_m` (index `m - 1`) and `FT(S') = FT(S)`. -/
theorem lemma_3 {m : ℕ} {J : Type*} [Fintype J] (F : FlowShop m J) (hm : 1 ≤ m)
    (S : PreemptiveSchedule F) :
    ∃ S' : PreemptiveSchedule F,
      S'.NoPreemptionOn ⟨0, by omega⟩ ∧ S'.NoPreemptionOn ⟨m - 1, by omega⟩ ∧
      S'.finishTime = S.finishTime := by sorry

end FlowJobShop.ThreePartFlow
