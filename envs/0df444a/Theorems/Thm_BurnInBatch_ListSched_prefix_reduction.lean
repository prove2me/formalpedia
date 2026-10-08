-- Prove2me | Theorems.Thm_BurnInBatch_ListSched_prefix_reduction
-- name    : BurnInBatch.ListSched.prefix_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:07:29.258197+00:00
-- url     : https://prove2.me/theorems/7095f9de-838b-46cb-966d-7e6d6ceeb520
-- title:
--   Proof of Proposition 4 — reduction to the critical batch prefix
-- statement:
--   Run BLS on an arbitrary ordering of all jobs. Suppose that batch $k$ contains a job whose lateness equals the run's maximum lateness $L$. Let $S_k$ contain exactly the jobs in the first $k+1$ batches; run BLS on that prefix alone, and write its maximum lateness as $L(S_k)$. Then
--
--   $$
--   L-L^*\le L(S_k)-L^*(S_k),
--   $$
--
--   where each optimum ranges over every valid batching and assignment of the indicated job set. This is the displayed prefix reduction in the proof of Proposition 4.
--
--   **Formalization Note** The prefix is the first $(k+1)B$ list entries, truncated at the end of the list. The assumption that batch $k$ contains a maximum-lateness job names the critical batch chosen in the paper's proof; it does not assume the displayed inequality. Processing times are positive and $B,m>0$.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 773, proof of Proposition 4, display “L − L* ≤ L − L*(S_k) = L(S_k) − L*(S_k)”; https://doi.org/10.1287/opre.40.4.764

import Mathlib
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.ListSched

/-- The displayed reduction in the proof of Proposition 4, p. 773.
If a job of batch `k` attains the BLS lateness, the first `k+1` batches
already attain it, while their optimum cannot exceed the full optimum. -/
theorem prefix_reduction {n : ℕ} (p d : Fin n → ℝ) (B m : ℕ)
    (l : List (Fin n)) (k : Fin (blsBatches B l).length)
    (hB : 0 < B) (hm : 0 < m) (hp : ∀ j, 0 < p j)
    (hl : ListsJobs Finset.univ l)
    (hmax : ∃ j ∈ (blsBatches B l)[k],
      jobCompletion p (blsBatches B l) (blsMachine p B m hm l) j - d j =
        blsLateness p d B m hm l Finset.univ) :
    blsLateness p d B m hm l Finset.univ - LStar p d B m Finset.univ ≤
      blsLateness p d B m hm (blsPrefix B l k) (blsPrefixJobs B l k) -
        LStar p d B m (blsPrefixJobs B l k) := by sorry

end BurnInBatch.ListSched
