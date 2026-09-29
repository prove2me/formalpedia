-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_168
-- name    : FiniteTriangular.sum_range_168
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:00:47.903952+00:00
-- url     : https://prove2.me/theorems/42fa24e4-7a56-4ac5-a81c-e46377d04570
-- title:
--   Sum of integers below 168
-- statement:
--   The sum of the nonnegative integers strictly less than $168$ equals $14028$. Equivalently, $\sum_{k=0}^{168-1} k = 168(168-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_168 : ∑ k ∈ range 168, k = 14028 := by sorry

end FiniteTriangular
