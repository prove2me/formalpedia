-- Prove2me | Theorems.Thm_BurnInBatch_BatchLPT_graham_lpt_bound
-- name    : BurnInBatch.BatchLPT.graham_lpt_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:23.370855+00:00
-- url     : https://prove2.me/theorems/262a8c96-13b4-4316-b651-6e4c112aa3cd
-- title:
--   §5, p. 772 — Graham's LPT bound $4/3 - 1/(3m)$ for $P//C_{\max}$, as quoted
-- statement:
--   This is **Graham's theorem** on the LPT rule (R. L. Graham, *Bounds on multiprocessing timing anomalies*, SIAM J. Appl. Math. 17 (1969)), quoted by Lee, Uzsoy and Martin-Vega.
--
--   Let $q_0 \ge q_1 \ge \dots \ge q_{M-1} \ge 0$ be the processing times of $M$ jobs listed in nonincreasing order, and $m \ge 1$ the number of identical machines. **List scheduling** takes the jobs in this order and assigns each to a machine of currently least load; write $C_{\mathrm{LPT}}$ for the resulting makespan (largest machine load). Let $C^*$ be the optimal makespan, the minimum of the largest machine load over all assignments of the $M$ jobs to the $m$ machines. Then
--   $$C_{\mathrm{LPT}} \le \left(\frac43 - \frac1{3m}\right) C^* .$$
--
--   In the paper this is the bound transferred to batch machines through Proposition 2 to give Proposition 3.
--
--   **Formalization Note.** Stated purely on the published definitions `listMakespan M m q` and `optMakespan M m q`, which only read $q_0, \dots, q_{M-1}$. Ties among least-loaded machines go to the lowest index (published rule); the bound holds for any tie rule. Nonnegative (rather than positive) times are allowed; zero-length jobs change nothing.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 772, §5 ("Graham has shown that for the P//C_max problem, this algorithm has a worst case error bound of (4/3 − 1/3m)"); quoted from R. L. Graham, Bounds on Multiprocessing Timing Anomalies, SIAM J. Appl. Math. 17 (1969) 416–429

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

theorem graham_lpt_bound {M m : ℕ} (hm : 0 < m) (q : ℕ → ℝ)
    (hq_nonneg : ∀ k, k < M → 0 ≤ q k)
    (hq_noninc : ∀ k k', k ≤ k' → k' < M → q k' ≤ q k) :
    listMakespan M m q ≤ (4 / 3 - 1 / (3 * (m : ℝ))) * optMakespan M m q := by sorry

end BurnInBatch.BatchLPT
