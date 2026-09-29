-- Prove2me | Theorems.Thm_BinPacking_FirstFit_ff_eq_bf_gt_seventeen_tenths_sub_eight
-- name    : BinPacking.FirstFit.ff_eq_bf_gt_seventeen_tenths_sub_eight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:08:14.41468+00:00
-- url     : https://prove2.me/theorems/56534d56-d142-47d3-87b2-c567e6abd5e7
-- title:
--   Theorem 2.1 — lists with $L^*=k$ and $FF(L)=BF(L)>1.7L^*-8$
-- statement:
--   For every integer $k\ge 1$ there exists a list $L$ of real numbers in $(0,1]$ with $L^*=k$ such that
--
--   $$FF(L)=BF(L)>1.7\,L^*-8.$$
--
--   This is the lower half of the asymptotic worst-case ratio $\tfrac{17}{10}$: the additive term of Theorem 2.2 cannot be traded for a smaller multiplicative constant, for either algorithm.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 301, Theorem 2.1

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model

namespace BinPacking.FirstFit

/-- Theorem 2.1 (p. 301): for every `k ≥ 1` there is a list `L` of reals in `(0, 1]` with
`L* = k` such that `FF(L) = BF(L) > 1.7 L* − 8`. -/
theorem ff_eq_bf_gt_seventeen_tenths_sub_eight (k : ℕ) (hk : 1 ≤ k) :
    ∃ L : List ℝ, IsList L ∧ optBins L = k ∧ FF L = BF L ∧
      17 / 10 * (k : ℝ) - 8 < (FF L : ℝ) := by sorry

end BinPacking.FirstFit
