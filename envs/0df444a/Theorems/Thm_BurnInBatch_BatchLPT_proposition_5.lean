-- Prove2me | Theorems.Thm_BurnInBatch_BatchLPT_proposition_5
-- name    : BurnInBatch.BatchLPT.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:33.086718+00:00
-- url     : https://prove2.me/theorems/f609d0fd-ba87-491c-8e57-0cdbc14a3e6a
-- title:
--   Proposition 5 — relative $L_{\max}$ error of BLPT is at most $(1/3 - 1/(3m)) + d_{\max}/(L^* + d_{\max})$
-- statement:
--   Consider $n \ge 1$ jobs with positive processing times $p_j$ and nonnegative due dates $d_j$, all available at time $0$, on $m \ge 1$ identical batch machines of capacity $B \ge 1$. Let $L$ be the maximum lateness $\max_j (C_j - d_j)$ of the schedule produced by Algorithm BLPT, $L^*$ the optimal maximum lateness of $P/B/L_{\max}$ (over all batchings, assignments and processing orders), and $d_{\max} = \max_j d_j$. Then
--   $$\frac{L - L^*}{L^* + d_{\max}} \le \left(\frac13 - \frac1{3m}\right) + \frac{d_{\max}}{L^* + d_{\max}} .$$
--
--   The ratio $(L - L^*)/(L^* + d_{\max})$ is used because $L^*$ may be negative; under the hypotheses $L^* + d_{\max} > 0$, so both fractions are well defined. Proposition 5 is the $L_{\max}$ counterpart of Proposition 3.
--
--   **Formalization Note.** The hypothesis $d_j \ge 0$ is not printed in the paper; its proof needs it (it uses $L^*(S_k) \ge C^*_{\max}(S_k) - d_{\max}$ and divides by $L^*(S_k) + d_{\max}$), and it guarantees $L^* + d_{\max} > 0$: for a job $j$ with $d_j = d_{\max}$, every schedule has $L_{\max} + d_{\max} \ge C_j \ge p_j > 0$. The bound is claimed for every BLPT run (every ranking `l` and every batch order `bl`, as in Proposition 3), with job completion times given by least-loaded list scheduling of the ordered batches.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 773, Proposition 5 (ratio defined on p. 773 before Proposition 4)

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model
import Definitions.Def_BurnInBatch_BatchLPT_BLPT

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

theorem proposition_5 {n m B : ℕ} (hn : 0 < n) (hm : 0 < m) (hB : 0 < B)
    (p d : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hd : ∀ j, 0 ≤ d j)
    (l : List (Fin n)) (hl : IsLPTList p l)
    (bl : List (Finset (Fin n))) (hbl : IsBLPTOrder p B l bl) :
    (blptLmax m p d bl - optLmax n m B p d) / (optLmax n m B p d + dMax d) ≤
      (1 / 3 - 1 / (3 * (m : ℝ))) + dMax d / (optLmax n m B p d + dMax d) := by sorry

end BurnInBatch.BatchLPT
