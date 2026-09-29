-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_50
-- name    : FiniteTriangular.sum_range_50
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:18:57.71929+00:00
-- url     : https://prove2.me/theorems/be4248de-b481-4984-b0ae-5abf8422d305
-- title:
--   Sum of integers below 50
-- statement:
--   The sum of the nonnegative integers strictly less than $50$ equals $1225$. Equivalently, $\sum_{k=0}^{50-1} k = 50(50-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_50 : ∑ k ∈ range 50, k = 1225 := by sorry

end FiniteTriangular
