-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_520
-- name    : FiniteTriangular.sum_range_520
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:23:56.648015+00:00
-- url     : https://prove2.me/theorems/60ddaaba-01b3-47d2-a542-fa7843895ef6
-- title:
--   Sum of integers below 520
-- statement:
--   The sum of the nonnegative integers strictly less than $520$ equals $134940$. Equivalently, $\\sum_{k=0}^{520-1} k = 520(520-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_520 : ∑ k ∈ range 520, k = 134940 := by sorry

end FiniteTriangular
