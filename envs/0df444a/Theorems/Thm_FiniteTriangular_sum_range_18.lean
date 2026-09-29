-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_18
-- name    : FiniteTriangular.sum_range_18
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:07:38.464606+00:00
-- url     : https://prove2.me/theorems/a6eea6ec-7304-49c3-a87e-3cf672f795a9
-- title:
--   Sum of integers below 18
-- statement:
--   The sum of the nonnegative integers strictly less than $18$ equals $153$. Equivalently, $\sum_{k=0}^{18-1} k = 18(18-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_18 : ∑ k ∈ range 18, k = 153 := by sorry

end FiniteTriangular
