-- Prove2me | Theorems.Thm_BurnInBatch_BatchLPT_proposition_3
-- name    : BurnInBatch.BatchLPT.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:54.953685+00:00
-- url     : https://prove2.me/theorems/19815e0d-bfe8-4e7a-819f-2b7f0cb0d9bd
-- title:
--   Proposition 3 — $C(\mathrm{BLPT}) \le (4/3 - 1/(3m))\,C^*$ on parallel batch machines
-- statement:
--   Consider $n$ jobs with positive processing times $p_j$, all available at time $0$, on $m \ge 1$ identical batch processing machines, each processing up to $B \ge 1$ jobs at a time, a batch taking as long as its longest job. Let $C^*$ be the optimal makespan of this problem $P/B/C_{\max}$, the minimum over all ways of forming batches and assigning them to machines. Let $C(\mathrm{BLPT})$ be the makespan produced by Algorithm BLPT: rank the jobs in nonincreasing order of processing time, group successive blocks of $B$ jobs into batches, order the batches in nonincreasing order of batch time and assign each in turn to a machine that becomes free first. Then
--   $$C(\mathrm{BLPT}) \le \left(\frac43 - \frac1{3m}\right) C^* .$$
--
--   For one machine the factor is $1$, so BLPT is then optimal. The proposition transfers Graham's worst-case bound for the LPT rule on ordinary parallel machines to batch machines.
--
--   **Formalization Note.** The bound is claimed for every run of BLPT: every ranking `l` nonincreasing in $p$ (ties arbitrary) and every ordering `bl` of its batches nonincreasing in batch time. "Assign them to the machines as they become free" is the published least-loaded list-scheduling rule. "$1/3m$" in the paper is $1/(3m)$. $C^*$ ranges over all valid batchings, not only the consecutive ones of Step 1.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 773, Proposition 3 (Algorithm BLPT, p. 772)

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model
import Definitions.Def_BurnInBatch_BatchLPT_BLPT

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

theorem proposition_3 {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (l : List (Fin n)) (hl : IsLPTList p l)
    (bl : List (Finset (Fin n))) (hbl : IsBLPTOrder p B l bl) :
    blptMakespan m p bl ≤ (4 / 3 - 1 / (3 * (m : ℝ))) * optBatchMakespan n m B p := by sorry

end BurnInBatch.BatchLPT
