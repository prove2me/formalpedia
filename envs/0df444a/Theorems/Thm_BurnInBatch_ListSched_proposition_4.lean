-- Prove2me | Theorems.Thm_BurnInBatch_ListSched_proposition_4
-- name    : BurnInBatch.ListSched.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:07:37.718784+00:00
-- url     : https://prove2.me/theorems/0984a4b4-1f14-4367-b5f7-434c3a4a4227
-- title:
--   Proposition 4 — relative maximum-lateness error of BLS
-- statement:
--   Let $n>0$ jobs have positive processing times $p_j$ and nonnegative due dates $d_j$. Fix a positive batch capacity $B$, a positive number $m$ of identical parallel machines, and **any** list containing each job once. Let $L$ be the maximum lateness of BLS on that list, $L^*$ the minimum maximum lateness over all valid batch schedules, and $d_{\max}$ the largest due date. Then
--
--   $$
--   \frac{L-L^*}{L^*+d_{\max}}
--   \le \left(B-\frac1m\right)+\frac{d_{\max}}{L^*+d_{\max}}.
--   $$
--
--   The normalization accommodates an optimal maximum lateness that can be negative. This result bounds BLS's relative maximum-lateness error using the batch capacity, machine count, and maximum due date.
--
--   **Formalization Note** The proof's last inequality requires $d_j\ge0$, a condition implicit in the paper's deadline setting but absent from its printed Proposition 4. Without it, the proposition can fail; for one job with $p=4$, $d=-3$, $B=1$, and $m=2$, its right side is negative while its left side is zero. Positive processing times and a nonempty instance ensure $L^*+d_{\max}>0$. The ratio has exactly the printed factor $B-1/m$.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 773, Proposition 4; https://doi.org/10.1287/opre.40.4.764

import Mathlib
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.ListSched

/-- Proposition 4, p. 773: the relative maximum-lateness error of BLS.
The hypothesis `hd` (nonnegative due dates) is not printed in the proposition; the
proof's last step `d_max - d^k ≤ d_max` uses it, and without it the statement fails
(one job, `p = 4`, `d = -3`, `B = 1`, `m = 2`). -/
theorem proposition_4 {n : ℕ} (p d : Fin n → ℝ) (B m : ℕ)
    (l : List (Fin n)) (hn : 0 < n) (hB : 0 < B) (hm : 0 < m)
    (hp : ∀ j, 0 < p j) (hd : ∀ j, 0 ≤ d j)
    (hl : ListsJobs Finset.univ l) :
    (blsLateness p d B m hm l Finset.univ - LStar p d B m Finset.univ) /
        (LStar p d B m Finset.univ + maxDue d hn) ≤
      ((B : ℝ) - 1 / (m : ℝ)) +
        maxDue d hn / (LStar p d B m Finset.univ + maxDue d hn) := by sorry

end BurnInBatch.ListSched
