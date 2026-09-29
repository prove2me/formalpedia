-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_33
-- name    : FiniteTriangular.sum_range_33
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:13:06.499324+00:00
-- url     : https://prove2.me/theorems/c16c52c5-aa15-4950-baa9-9ed1e0c613df
-- title:
--   Sum of integers below 33
-- statement:
--   The sum of the nonnegative integers strictly less than $33$ equals $528$. Equivalently, $\sum_{k=0}^{33-1} k = 33(33-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_33 : ∑ k ∈ range 33, k = 528 := by sorry

end FiniteTriangular
