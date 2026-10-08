-- Prove2me | Theorems.Thm_BurnInBatch_TardyJobs_lemma_5
-- name    : BurnInBatch.TardyJobs.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:15.119094+00:00
-- url     : https://prove2.me/theorems/1de0540b-6b93-477e-8874-d0f933ceb5f9
-- title:
--   Lemma 5 — on-time batches can contain consecutive jobs
-- statement:
--   Consider the equal-processing-time batch problem with capacity $B\ge1$ and jobs indexed so that release times and due dates are both nondecreasing. There is an optimal complete schedule in which every batch whose jobs all finish on time consists of consecutive indices. If such a batch has $k$ jobs and first index $a$, its set of jobs is
--
--   $$
--   \{a,a+1,\ldots,a+k-1\}.
--   $$
--
--   This existence claim supplies the consecutive-last-batch structure used by DP3 without narrowing the optimization problem's feasible schedules.
--
--   **Formalization Note** The paper states agreeable releases and due dates and then fixes due-date index order for this section. Both sequences are required to be nondecreasing so a batch's last index has its latest release; tied due dates are ordered by release time.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 770, Lemma 5

import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model

namespace BurnInBatch.TardyJobs

/-- Lemma 5, p. 770: in an optimum, every entirely on-time batch
consists of consecutive job indices. -/
theorem lemma_5 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hB : 0 < B) (hd : Monotone d) (hr : Monotone r) :
    ∃ S : List (Finset (Fin n)),
      Optimal B (equalTime p) r d S ∧
      ∀ P ∈ S,
        (∀ j ∈ P, jobCompletion (equalTime p) r S j ≤ d j) → Consecutive P := by sorry

end BurnInBatch.TardyJobs
