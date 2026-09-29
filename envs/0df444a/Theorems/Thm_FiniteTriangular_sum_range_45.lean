-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_45
-- name    : FiniteTriangular.sum_range_45
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:17:12.965988+00:00
-- url     : https://prove2.me/theorems/e14495ee-671f-4158-abe5-f0276a6e5580
-- title:
--   Sum of integers below 45
-- statement:
--   The sum of the nonnegative integers strictly less than $45$ equals $990$. Equivalently, $\sum_{k=0}^{45-1} k = 45(45-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_45 : ∑ k ∈ range 45, k = 990 := by sorry

end FiniteTriangular
