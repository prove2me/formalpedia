-- Prove2me | Theorems.Thm_BinPacking_Decreasing_ffd_eq_bfd_gt_eleven_ninths_sub_two
-- name    : BinPacking.Decreasing.ffd_eq_bfd_gt_eleven_ninths_sub_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:17:57.904813+00:00
-- url     : https://prove2.me/theorems/db2494d8-2a57-4f1c-8c0b-5a127b96092a
-- title:
--   Theorem 3.1 — for every $k\ge1$ some list with $L^*=k$ has $FFD(L)=BFD(L)>\frac{11}{9}L^*-2$
-- statement:
--   For every integer $k\ge 1$ there is a list $L$ of real numbers in $(0,1]$ whose optimum is exactly $L^*=k$ and on which First-Fit Decreasing and Best-Fit Decreasing use the same number of bins, with
--   $$FFD(L)=BFD(L)>\frac{11}{9}\,L^*-2 .$$
--
--   This is the lower bound matching Theorem 3.2: the ratio $11/9$ cannot be improved, so $\lim_{k\to\infty}R_{FFD}(k)=\lim_{k\to\infty}R_{BFD}(k)=11/9$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 308, Theorem 3.1

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.Decreasing

/-- Theorem 3.1 (p. 308): for each `k ≥ 1` there is a list `L` of reals in `(0, 1]` with
`L* = k` such that `FFD(L) = BFD(L) > (11/9) L* − 2`. -/
theorem ffd_eq_bfd_gt_eleven_ninths_sub_two (k : ℕ) (hk : 1 ≤ k) :
    ∃ L : List ℝ, IsList L ∧ optBins L = k ∧ FFD L = BFD L ∧
      (11 / 9 : ℝ) * (optBins L : ℝ) - 2 < (FFD L : ℝ) := by sorry

end BinPacking.Decreasing
