-- Prove2me | Theorems.Thm_DynamicOnlineLP_LowerBound_hard_opt_le
-- name    : DynamicOnlineLP.LowerBound.hard_opt_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T20:05:44.645785+00:00
-- url     : https://prove2.me/theorems/2c69be64-b343-4c2f-a69d-599b89e042f1
-- title:
--   Appendix C — the offline optimum of the constructed instance is at most 7B
-- statement:
--   Let $z\ge 1$, $k\ge 0$, $m=2^z$ and $B=zk$, and consider the constructed instance of the lower-bound construction: for each pair $i$, $k$ inputs $(4,v_i)$, $q_i$ inputs $(3,w_i)$, $s$ inputs $(2,w_i)$ and $2k-q_i$ inputs $(1,w_i)$, where $v_{ij}$ is the $i$-th bit of item $j$ and $w_{ij}=1-v_{ij}$, with $q_i\le 2k$ and any $s\ge 0$, and capacity $B$ for each of the $m$ items. Then the optimal value of the offline linear program (maximize $\sum_c \pi_c x_c$ subject to $\sum_c a_{jc}x_c\le B$ for every item $j$ and $0\le x_c\le 1$) satisfies
--
--   $$\mathrm{OPT}\le 7B.$$
--
--   The reason given on the page: every set of demand vectors consisting of either $v_i$ or $w_i$ for each $i$ has an item in common, only $B$ units of it are available, so at most $2B$ demand vectors can be accepted, giving profit at most $7B$. The bound is used in the proof of Claim 1 and in the final step of the proof of Theorem 2, where a loss of order $\sqrt{zB}$ is converted into a loss of order $\sqrt{z/B}$ in the competitive ratio.
--
--   **Formalization Note** Fractional solutions $x_c\in[0,1]$ are allowed, as in the linear program (1). $\mathrm{OPT}$ is the supremum of the objective over the (nonempty, bounded) feasible set. The count $s$ of profit-2 inputs is arbitrary; the paper's value $\sqrt{B/4z}$ is a special case.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, Appendix C, pp. 888–889 ("Now, observe that OPT ⩽ 7B …"); also used in the proof of Claim 1, p. 886

import Mathlib
import Definitions.Def_DynamicOnlineLP_LowerBound_OnlineLP
import Definitions.Def_DynamicOnlineLP_LowerBound_HardInstance

namespace DynamicOnlineLP.LowerBound

/-- Agrawal–Wang–Ye 2014, Appendix C (p. 889) and proof of Claim 1 (p. 886): the offline optimum
of the constructed instance (`m = 2^z` items, `B = z k` units of each, `B/z = k`) is at most `7B`. -/
theorem hard_opt_le (z k s : ℕ) (hz : 1 ≤ z) (q : Fin z → ℕ) (hq : ∀ i, q i ≤ 2 * k) :
    OPT (hardProfit z k s q) (hardDemand z k s q) (hardCapacity z k)
      ≤ 7 * ((z : ℝ) * (k : ℝ)) := by sorry

end DynamicOnlineLP.LowerBound
