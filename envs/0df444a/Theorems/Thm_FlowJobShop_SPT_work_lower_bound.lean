-- Prove2me | Theorems.Thm_FlowJobShop_SPT_work_lower_bound
-- name    : FlowJobShop.SPT.work_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:38:02.735517+00:00
-- url     : https://prove2.me/theorems/37eef098-d325-4a63-a644-c7453b501051
-- title:
--   Proof of Lemma 9 — $f_{i_k}(S^*)\ge\sum_{j\le k}L_{i_j}/m$ along the finishing order
-- statement:
--   Let a job shop with $m$ processors and $n$ jobs be given, $L_i$ the total task time of job $i$, and $\tau$ any feasible non-preemptive schedule. Let $\rho(0),\rho(1),\dots,\rho(n-1)$ be an order in which the jobs finish in $\tau$, that is, a bijection with $f_{\rho(0)}(\tau)\le f_{\rho(1)}(\tau)\le\cdots\le f_{\rho(n-1)}(\tau)$. Then for every $k$,
--   $$
--   \sum_{j=0}^{k} L_{\rho(j)}\ \le\ m\cdot f_{\rho(k)}(\tau).
--   $$
--   Equivalently $f_{i_k}(\tau)\ge\sum_{j=1}^k L_{i_j}/m$, where $i_1,\dots,i_n$ is the finishing order. This is the first lower-bound step of the proof of Lemma 9, applied there to an OMFT schedule $S^*$; it holds for every feasible schedule.
--
--   **Formalization Note** Positions are 0-based and the inequality is multiplied by $m$, so no division by $m$ occurs. Feasibility allows zero-time tasks to occupy no processor interval. The paper assumes $m\ge1$.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 47, §2, proof of Lemma 9 ('For S* we have f_{i_k}(S*) ≥ Σ_{j=1}^k L_{i_j}/m')

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime

open JobShopLTAS.Core

namespace FlowJobShop.SPT

/-- Let `τ` be any feasible non-preemptive schedule of an `m`-processor job shop, and let
`ρ 0, ρ 1, …` be the order in which the jobs finish in `τ` (finish times nondecreasing).
Then for every `k`, `m · f_{ρ k}(τ) ≥ ∑_{j ≤ k} L_{ρ j}` (Gonzalez–Sahni 1978, proof of Lemma 9,
p. 47: `f_{i_k}(S*) ≥ ∑_{j=1}^k L_{i_j}/m`, multiplied by `m`). -/
theorem work_lower_bound {m n : ℕ} (inst : Instance m n) (hm : 0 < m) (τ : inst.Op → ℝ)
    (hτ : IsPaperFeasibleSchedule inst τ) (ρ : Fin n ≃ Fin n)
    (hρ : Monotone fun k => finishTime inst τ (ρ k)) (k : Fin n) :
    ∑ j ∈ Finset.Iic k, inst.jobLength (ρ j) ≤ (m : ℝ) * finishTime inst τ (ρ k) := by sorry

end FlowJobShop.SPT
