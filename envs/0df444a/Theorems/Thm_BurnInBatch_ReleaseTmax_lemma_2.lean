-- Prove2me | Theorems.Thm_BurnInBatch_ReleaseTmax_lemma_2
-- name    : BurnInBatch.ReleaseTmax.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:28:59.987659+00:00
-- url     : https://prove2.me/theorems/d62f6644-16fb-4e34-a148-bcfeeab8190d
-- title:
--   Lemma 2 — some schedule has $T_{\max} \le (n-1)p$ (assuming $r_j + p \le d_j$)
-- statement:
--   Consider one batch machine of capacity $B \ge 1$ and $n$ jobs with common processing time $p$, release times $r_i$ and due dates $d_i$ that are agreeable ($r_i < r_j$ implies $d_i \le d_j$), and assume that every job can meet its due date if it is started at its release time:
--   $$
--   r_j + p \le d_j \qquad (j = 1, \dots, n).
--   $$
--   Then some batch schedule of all $n$ jobs has maximum tardiness
--   $$
--   T_{\max} = \max_j \max\{0, C_j - d_j\} \le (n-1)p .
--   $$
--   The lemma supplies the upper end of the search interval for the bisection on $T_{\max}$ (Algorithm 1).
--
--   **Formalization Note** The hypothesis $r_j + p \le d_j$ is not in the printed statement of Lemma 2; its proof says "Since by assumption $r_j + p < d_j$", and the lemma is false without it (one job with $r = d = 0$, $p = 1$ has $T_{\max} = 1 > 0 = (n-1)p$). The weak inequality used here is a weaker hypothesis than the strict one of the proof. "An upper bound on the value of $T_{\max}$" is read as a bound on the optimal value: some schedule achieves it, not every schedule. Agreeability is in the paper's statement and is kept. The time bound of Corollary 1 is not formalized.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 769, Lemma 2 and its proof ("by assumption r_j + p < d_j")

import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model

namespace BurnInBatch.ReleaseTmax

/-- Lemma 2 (p. 769), with the assumption `r_j + p ≤ d_j` of its proof. One batch machine of
capacity `B ≥ 1`, `n` jobs with common processing time `p`, agreeable release times and due
dates, and `r_j + p ≤ d_j` for every job. Then some batch schedule of all `n` jobs has maximum
tardiness at most `(n − 1)p`. -/
theorem lemma_2 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) (hB : 0 < B)
    (hagree : ∀ i j : Fin n, r i < r j → d i ≤ d j)
    (hrd : ∀ j : Fin n, r j + p ≤ d j) :
    ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ tmax p r d Finset.univ S ≤ (n - 1) * p := by sorry

end BurnInBatch.ReleaseTmax
