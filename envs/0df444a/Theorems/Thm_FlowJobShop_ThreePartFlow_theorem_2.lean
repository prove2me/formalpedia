-- Prove2me | Theorems.Thm_FlowJobShop_ThreePartFlow_theorem_2
-- name    : FlowJobShop.ThreePartFlow.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:37:22.455656+00:00
-- url     : https://prove2.me/theorems/1b7223b8-1158-4e87-bf61-e8d8f2558756
-- title:
--   Theorem 2 — the 3-Partition flow shop on three machines has a preemptive schedule of finish time ≤ 2tB iff a 3-partition exists
-- statement:
--   The paper states: *Preemptive FOFT with $m=3$ and the problem size being measured as the sum of the length of the tasks is NP-complete.* Its proof combines Lemma 4 (the reduction 3-Partition $\propto$ preemptive FOFT) with Lemma 2 (membership in NP). What Lemma 4 establishes, and what is formalized here, is the following.
--
--   Let $C=(a_1,\dots,a_s,B)$ with $s=3t$ and $t\ge 2$ be an instance of 3-Partition: $B$ is a positive integer, $\sum_{i=1}^s a_i=tB$ and $B/4<a_i<B/2$ for every $i$. Let $FS$ be the three-processor flow shop with $s+t+2$ jobs constructed from $C$ in the proof of Lemma 4. Then
--
--   1. $FS$ has a preemptive schedule $S$ with $FT(S)\le 2tB$ if and only if $C$ has a partition into $t$ three-element sets each of sum $B$; and
--   2. every task time of $FS$ is at most $2B$:
--   $$t_{j,i}\le 2B\qquad\text{for all processors } j \text{ and jobs } i.$$
--
--   Part 2 is the formal trace of "the problem size being measured as the sum of the length of the tasks": the instance's numbers are polynomial in the numbers of $C$, which is what makes the result NP-completeness in the strong sense.
--
--   **Formalization Note** "NP-complete", the reduction symbol $\propto$ and membership in NP (Lemma 2) are not formalized; the theorem states the equivalence that the reduction rests on, for the instance the proof constructs, together with the bound on its task times. The hypothesis $t\ge 2$ is not in the paper; the construction needs it, because for $t<2$ the job indices $s+1$ and $s+t$ coincide with conflicting times.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 41, Theorem 2 and Lemma 4 (proof pp. 41–42)

import Mathlib
import Definitions.Def_FlowJobShop_ThreePartFlow_FlowShop
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_FlowJobShop_ThreePartFlow_Instance

open ResourceScheduling.Chain
open FlowJobShop.ThreePartFlow.FlowShop

namespace FlowJobShop.ThreePartFlow

/-- Theorem 2 (Gonzalez–Sahni 1978, p. 41), in the form its proof establishes (Lemma 4): for
every 3-Partition instance `C = (a_1, …, a_s, B)`, `s = 3t`, `t ≥ 2`, the three-processor
flow shop `FS` built from `C` has a preemptive schedule with finish time `≤ 2tB` iff `C` has a
3-partition; moreover every task time of `FS` is at most `2B` (the reduction's trace of
measuring the problem size by the sum of the task lengths). -/
theorem theorem_2 (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t) :
    ((∃ S : PreemptiveSchedule (FS C), S.finishTime ≤ tau C) ↔ C.HasSolution) ∧
      ∀ j i, (FS C).t j i ≤ 2 * (C.b : ℝ) := by sorry

end FlowJobShop.ThreePartFlow
