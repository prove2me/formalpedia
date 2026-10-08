-- Prove2me | Theorems.Thm_FlowJobShop_SPT_mft_lower_bound
-- name    : FlowJobShop.SPT.mft_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:38:49.445646+00:00
-- url     : https://prove2.me/theorems/b68d4970-2c0e-405e-b96f-c9b6ec52a8a7
-- title:
--   Proof of Lemma 9 — $\mathrm{MFT}(S^*)\ge(1/n)\sum_{k}\sum_{j\le k}L_j/m$
-- statement:
--   Let a job shop with $m$ processors and $n$ jobs be given, $L_i$ the total task time of job $i$, $\sigma$ an SPT order ($L_{\sigma(0)}\le\cdots\le L_{\sigma(n-1)}$), and $\tau$ any feasible non-preemptive schedule. Then
--   $$
--   \frac1n\sum_{k=0}^{n-1}\sum_{j=0}^{k}L_{\sigma(j)}\ \le\ m\cdot\mathrm{MFT}(\tau).
--   $$
--   This is the lower bound $\mathrm{MFT}(S^*)\ge(1/n)\sum_{k=1}^n\sum_{j=1}^k L_j/m$ of the proof of Lemma 9, multiplied by $m$, for every feasible schedule and hence for an OMFT schedule $S^*$. Together with the upper bound on the SPT schedule it gives Lemma 9.
--
--   **Formalization Note** Positions are 0-based; for $n=0$ both sides are $0$ (Lean's $x/0=0$). The bound is multiplied by $m$ instead of divided by it. The paper assumes $m\ge1$.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 47, §2, proof of Lemma 9 ('and so MFT(S*) ≥ (1/n) Σ_{k=1}^n Σ_{j=1}^k L_j/m')

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime
import Definitions.Def_FlowJobShop_SPT_ListSchedule

open JobShopLTAS.Core

namespace FlowJobShop.SPT

/-- For every feasible non-preemptive schedule `τ` of an `m`-processor, `n`-job job shop and every
SPT order `σ`, `m · MFT(τ) ≥ (1/n) ∑_{k} ∑_{j ≤ k} L_{σ j}` (Gonzalez–Sahni 1978, proof of
Lemma 9, p. 47: `MFT(S*) ≥ (1/n) ∑_{k=1}^n ∑_{j=1}^k L_j/m`, multiplied by `m`). -/
theorem mft_lower_bound {m n : ℕ} (inst : Instance m n) (hm : 0 < m) (σ : Fin n ≃ Fin n)
    (hσ : IsSPTOrder inst σ) (τ : inst.Op → ℝ) (hτ : IsPaperFeasibleSchedule inst τ) :
    (∑ k : Fin n, ∑ j ∈ Finset.Iic k, inst.jobLength (σ j)) / n ≤
      (m : ℝ) * meanFlowTime inst τ := by sorry

end FlowJobShop.SPT
