-- Prove2me | Theorems.Thm_FlowJobShop_SPT_listSchedule_finishTime_le
-- name    : FlowJobShop.SPT.listSchedule_finishTime_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:38:40.406408+00:00
-- url     : https://prove2.me/theorems/b9b211c3-7b63-48d7-b400-8b62ca987686
-- title:
--   Proof of Lemma 9 — in the SPT schedule, $f_i(S)\le\sum_{j\le i}L_j$
-- statement:
--   Let a job shop with $m$ processors and $n$ jobs be given, $L_i$ the total task time of job $i$, and $\sigma$ any order of the jobs. In the list schedule $S$ that processes the jobs $\sigma(0),\sigma(1),\dots$ in turn, the job in position $k$ finishes no later than the total task time of the jobs in positions $0,\dots,k$:
--   $$
--   f_{\sigma(k)}(S)\le\sum_{j=0}^{k} L_{\sigma(j)} .
--   $$
--   With the jobs renumbered so that $L_1\le\cdots\le L_n$, this is the step $f_i(S)\le\sum_{j=1}^i L_j$ of the proof of Lemma 9, which bounds the mean flow time of the SPT schedule by $\frac1n\sum_{i=1}^n\sum_{j=1}^i L_j$.
--
--   **Formalization Note** Positions are 0-based. The inequality is stated for every order $\sigma$; the paper uses it for an SPT order. The paper assumes $m\ge1$.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 47, §2, proof of Lemma 9 ('Then f_i(S) ≤ Σ_1^i L_j')

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime
import Definitions.Def_FlowJobShop_SPT_ListSchedule

open JobShopLTAS.Core

namespace FlowJobShop.SPT

/-- In the list schedule that processes the jobs in the order `σ`, the job in position `k`
finishes no later than the total task time of the jobs in positions `0, …, k`:
`f_{σ k}(S) ≤ ∑_{j ≤ k} L_{σ j}` (Gonzalez–Sahni 1978, proof of Lemma 9, p. 47). -/
theorem listSchedule_finishTime_le {m n : ℕ} (inst : Instance m n) (hm : 0 < m)
    (σ : Fin n ≃ Fin n)
    (k : Fin n) :
    finishTime inst (listSchedule inst σ) (σ k) ≤
      ∑ j ∈ Finset.Iic k, inst.jobLength (σ j) := by sorry

end FlowJobShop.SPT
