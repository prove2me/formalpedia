-- Prove2me | Theorems.Thm_BurnInBatch_BatchLPT_reduction_to_unit_capacity
-- name    : BurnInBatch.BatchLPT.reduction_to_unit_capacity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:28.056794+00:00
-- url     : https://prove2.me/theorems/32c02ed0-ae62-4ece-aa99-5c6e6ffaf0fd
-- title:
--   §5, p. 772 — $P/B/C_{\max}$ equals the unit-capacity $P//C_{\max}$ problem on the aggregate batch jobs
-- statement:
--   Let $n$ jobs with positive processing times $p_j$ be scheduled on $m \ge 1$ identical batch machines of capacity $B \ge 1$. Rank the jobs in nonincreasing order of processing time (ties in any order) and let $B_1, \dots, B_M$, $M = \lceil n/B \rceil$, be the successive groups of $B$ jobs of the ranked list. View each batch as a single **aggregate job** of length $p(B_k) = \max_{j \in B_k} p_j$. Then the optimal makespan of the batch problem equals the optimal makespan of the ordinary (unit-capacity) parallel-machine problem $P//C_{\max}$ on the aggregate jobs:
--   $$C^* = \min_{\sigma : \{1,\dots,M\} \to \{1,\dots,m\}}\ \max_{i}\ \sum_{k : \sigma(k) = i} p(B_k).$$
--
--   This is the reduction the paper draws from Proposition 2; it is what allows Graham's analysis of LPT for $P//C_{\max}$ to be transferred to the batch problem.
--
--   **Formalization Note.** The right-hand side is the published `optMakespan` on the item sequence of batch times of `blptBatches B l`; the left-hand side `optBatchMakespan` ranges over every valid batching.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 772, §5, text after Proposition 2: "Thus, the P/B/C_max problem can be viewed as an equivalent unit capacity machine P//C_max problem"

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model
import Definitions.Def_BurnInBatch_BatchLPT_BLPT

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

theorem reduction_to_unit_capacity {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (l : List (Fin n)) (hl : IsLPTList p l) :
    optBatchMakespan n m B p =
      optMakespan (blptBatches B l).length m (BurnInBatch.ListSched.batchTimes p (blptBatches B l)) := by sorry

end BurnInBatch.BatchLPT
