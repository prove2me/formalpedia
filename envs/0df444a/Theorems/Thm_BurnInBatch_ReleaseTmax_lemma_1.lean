-- Prove2me | Theorems.Thm_BurnInBatch_ReleaseTmax_lemma_1
-- name    : BurnInBatch.ReleaseTmax.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:28:54.425233+00:00
-- url     : https://prove2.me/theorems/932d9617-9007-435c-b364-1a795a2847e3
-- title:
--   Lemma 1 — an on-time schedule can be rearranged into batch-EDD order
-- statement:
--   Consider one batch machine of capacity $B$ and $n$ jobs with common processing time $p$, release times $r_i$ and due dates $d_i$, where release times and due dates are **agreeable**: $r_i < r_j$ implies $d_i \le d_j$.
--
--   If there is a batch schedule of all $n$ jobs in which every job is on time ($T_{\max} = 0$), then there is a batch schedule of all $n$ jobs in which every job is on time and the batches are in **batch-EDD order**: whenever batch $P$ is processed before batch $Q$, no $i \in P$ and $j \in Q$ satisfy $d_i > d_j$.
--
--   The lemma is the exchange argument that makes the batches of an on-time schedule respect the due-date order; it is the first step toward the consecutive structure that Algorithm DP1 exploits.
--
--   **Formalization Note** The paper prints agreeability as "$r_i \le r_j$ implies $d_i \le d_j$", which read literally forces equal due dates for equal release times. The strict form used here is a weaker hypothesis, so the Lean statement implies the printed one. Lemma 1 itself needs no assumption on the job indexing.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 767, Lemma 1 (with Definition 1)

import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model

namespace BurnInBatch.ReleaseTmax

/-- Lemma 1 (p. 767). One batch machine of capacity `B`, `n` jobs with common processing time
`p`, release times `r` and due dates `d` that are agreeable (`r_i < r_j → d_i ≤ d_j`). If some
batch schedule of all `n` jobs has every job on time (`T_max = 0`), then some batch schedule of
all `n` jobs has every job on time and is in batch-EDD order. -/
theorem lemma_1 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hagree : ∀ i j : Fin n, r i < r j → d i ≤ d j)
    (hfeas : ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ AllOnTime p r d Finset.univ S) :
    ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ AllOnTime p r d Finset.univ S ∧ IsBatchEDD d S := by sorry

end BurnInBatch.ReleaseTmax
