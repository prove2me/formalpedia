-- Prove2me | Theorems.Thm_BinPacking_FirstFit_weight_sum_le_seventeen_tenths
-- name    : BinPacking.FirstFit.weight_sum_le_seventeen_tenths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:05:40.919844+00:00
-- url     : https://prove2.me/theorems/449287ba-4666-452d-9323-ea89fc5c3e2d
-- title:
--   Claim 2.2.1 — a bin of total size at most 1 has weight at most 17/10
-- statement:
--   Let $W$ be the weighting function of the First-Fit analysis. Let a bin be filled with numbers $b_1,b_2,\dots,b_m\in(0,1]$ whose sum is at most $1$. Then
--
--   $$\sum_{i=1}^m W(b_i)\le\frac{17}{10}.$$
--
--   This is the only place where the capacity of a bin enters the upper bound: summing it over an optimal packing shows that the total weight of a list $L$ is at most $\tfrac{17}{10}L^*$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 304, Claim 2.2.1

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model
import Definitions.Def_BinPacking_FirstFit_W

namespace BinPacking.FirstFit

/-- Claim 2.2.1 (p. 304): if a bin is filled with `b₁, …, b_m` (reals in `(0, 1]` with sum at
most `1`), then `Σ W(b_i) ≤ 17/10`. -/
theorem weight_sum_le_seventeen_tenths (bs : List ℝ) (hbs : IsList bs) (hsum : bs.sum ≤ 1) :
    (bs.map W).sum ≤ 17 / 10 := by sorry

end BinPacking.FirstFit
