-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_47
-- name    : FiniteTriangular.sum_range_47
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:17:11.13218+00:00
-- url     : https://prove2.me/theorems/1702469d-2c68-4158-a80a-2cc1a972d3c3
-- title:
--   Sum of integers below 47
-- statement:
--   The sum of the nonnegative integers strictly less than $47$ equals $1081$. Equivalently, $\sum_{k=0}^{47-1} k = 47(47-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_47 : ∑ k ∈ range 47, k = 1081 := by sorry

end FiniteTriangular
