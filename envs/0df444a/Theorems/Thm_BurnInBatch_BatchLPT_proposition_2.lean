-- Prove2me | Theorems.Thm_BurnInBatch_BatchLPT_proposition_2
-- name    : BurnInBatch.BatchLPT.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:33.902904+00:00
-- url     : https://prove2.me/theorems/2596e977-bd32-4904-9845-5c45e988c6b6
-- title:
--   Proposition 2 — some optimal $P/B/C_{\max}$ schedule uses exactly the full batches of consecutive longest jobs
-- statement:
--   Consider $n$ jobs with positive processing times $p_j$ on $m \ge 1$ identical batch processing machines of capacity $B \ge 1$, all jobs available at time $0$. Re-index the jobs in nonincreasing order of processing time, $p_{j_1} \ge \dots \ge p_{j_n}$ (ties in any order), and let
--   $$B_1 = \{j_1, \dots, j_B\},\ B_2 = \{j_{B+1}, \dots, j_{2B}\},\ \dots,\ B_{\lceil n/B\rceil}$$
--   be the successive groups of $B$ consecutive jobs, the last one possibly smaller.
--
--   **Proposition 2.** There is an optimal schedule of $P/B/C_{\max}$, that is, a valid batching $S$ and an assignment $\sigma$ of its batches to machines with makespan equal to $C^*$, whose batches are exactly $B_1, \dots, B_{\lceil n/B\rceil}$ (in some order).
--
--   Being exactly these sets is the paper's statement that "all batches will contain consecutive jobs" and "all batches, except possibly the one containing the highest indexed job, will be full": a partition of the ranked list into intervals of consecutive jobs, all of size $B$ except the one containing the last job, is exactly $B_1, B_2, \dots$. The result fixes the batch structure of an optimal schedule in advance.
--
--   **Formalization Note.** The ranking is any list `l` of all jobs, nonincreasing in $p$; the statement holds for every such list. $C^*$ ranges over all valid batchings (any sizes $\le B$, any grouping), not only over consecutive ones.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 772, Proposition 2

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model
import Definitions.Def_BurnInBatch_BatchLPT_BLPT

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

theorem proposition_2 {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (l : List (Fin n)) (hl : IsLPTList p l) :
    ∃ S : List (Finset (Fin n)), ∃ σ : Fin S.length → Fin m,
      IsBatching n B S ∧ S.Perm (blptBatches B l) ∧
      makespan (BurnInBatch.ListSched.batchTimes p S) σ = optBatchMakespan n m B p := by sorry

end BurnInBatch.BatchLPT
