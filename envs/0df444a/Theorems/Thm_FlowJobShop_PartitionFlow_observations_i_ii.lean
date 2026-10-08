-- Prove2me | Theorems.Thm_FlowJobShop_PartitionFlow_observations_i_ii
-- name    : FlowJobShop.PartitionFlow.observations_i_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:34:06.399995+00:00
-- url     : https://prove2.me/theorems/7d344e6e-0d6e-4af7-a68f-76385a26b5b0
-- title:
--   Lemma 1(b), observations (i)–(ii): in a schedule of FS with finish time $\le 2T$, $t_{1,n+1}$ ends by $T$ and $t_{3,n+2}$ starts after $T$
-- statement:
--   Let $S=\{a_1,\dots,a_n\}$, $T=\sum_i a_i$ and FS be as in the proof of Lemma 1. Let $S'$ be any preemptive schedule of FS with $\mathrm{FT}(S')\le 2T$. Then
--
--   1. task $t_{1,n+1}$ finishes by time $T$: every piece of it ends at or before $T$;
--   2. task $t_{3,n+2}$ does not start before time $T$: every piece of it starts at or after $T$.
--
--   These two observations are the first step of the paper's proof of Lemma 1(b): they fix the window $[0,T]$ in which the other jobs can use processor $P_1$, and the window $[T,2T]$ that job $n+2$ needs on $P_3$.
--
--   **Formalization Note** "Finishes by $T$" and "does not start before $T$" are stated piecewise; when $T=0$ both tasks have time $0$, have no piece, and the statement holds trivially, as in the paper.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 39, §1 Flow Shop, proof of Lemma 1, observations (i) and (ii)

import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Observations (i)–(ii) in the proof of Lemma 1(b) (Gonzalez–Sahni 1978, p. 39): in every
preemptive schedule of FS with finish time `≤ 2T`, (i) task `t_{1,n+1}` finishes by time `T`
(every piece of it ends by `T`), and (ii) task `t_{3,n+2}` does not start before time `T`
(every piece of it starts at or after `T`). Job `n + 1` is `Sum.inr 0`, job `n + 2` is
`Sum.inr 1`; processors `P_1, P_3` are `0, 2`. -/
theorem observations_i_ii {n : ℕ} (a : Fin n → ℕ) (S : PreemptiveSchedule (FS a))
    (hS : S.finishTime ≤ 2 * T a) :
    (∀ p ∈ S.pieces 0 (Sum.inr 0), p.2 ≤ T a) ∧
      (∀ p ∈ S.pieces 2 (Sum.inr 1), T a ≤ p.1) := by sorry

end FlowJobShop.PartitionFlow
