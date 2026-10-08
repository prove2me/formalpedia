-- Prove2me | Theorems.Thm_BurnInBatch_AgreeTmax_lemma_3
-- name    : BurnInBatch.AgreeTmax.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:29:41.188121+00:00
-- url     : https://prove2.me/theorems/c18088b1-93dc-47ea-9795-a3fe4b96b62f
-- title:
--   Lemma 3 — with agreeable processing times and due dates, a schedule with $T_{\max}=0$ can be taken in batch-EDD order
-- statement:
--   Consider $n$ jobs on a single batch processing machine of capacity $B\ge 1$, all available at time $0$, with processing times $p_i$ and due dates $d_i$ that are **agreeable**: $p_i<p_j$ implies $d_i\le d_j$. A batch takes the processing time of its longest job, and batches run back to back.
--
--   If some batch schedule of all $n$ jobs has maximum tardiness $T_{\max}=0$, then some batch schedule $S$ of all $n$ jobs has
--   $$T_{\max}(S)=0\quad\text{and}\quad S \text{ is in batch-EDD order,}$$
--   that is, whenever batch $P$ is processed before batch $Q$, no $i\in P$, $j\in Q$ have $d_i>d_j$.
--
--   This is the structural property that turns the search for a feasible schedule into a search over sequences ordered by due date, on which Algorithm DP2 is built.
--
--   **Formalization Note** The paper states agreeability as "$p_i\le p_j$ implies $d_i\le d_j$"; the hypothesis here is the strict form $p_i<p_j\Rightarrow d_i\le d_j$, which is weaker, so this statement implies the printed lemma. No indexing assumption is needed.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 769, Lemma 3

import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model

namespace BurnInBatch.AgreeTmax

/-- Lemma 3 of Lee, Uzsoy & Martin-Vega (1992), p. 769: in `1/B/T_max` with agreeable processing
times and due dates (strict form `p i < p j → d i ≤ d j`), if some valid batch schedule of all `n`
jobs has `T_max = 0`, then some valid batch schedule with `T_max = 0` is in batch-EDD order. -/
theorem lemma_3 {n B : ℕ} (hB : 0 < B) (p d : Fin n → ℕ) (hagr : Agreeable p d)
    (hfeas : ∃ S : List (Finset (Fin n)), IsValid B Finset.univ S ∧ Tmax p d S = 0) :
    ∃ S : List (Finset (Fin n)), IsValid B Finset.univ S ∧ Tmax p d S = 0 ∧ IsBatchEDD d S := by sorry

end BurnInBatch.AgreeTmax
