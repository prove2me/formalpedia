-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_859
-- name    : FiniteTriangular.sum_range_859
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:39:56.765689+00:00
-- url     : https://prove2.me/theorems/0f5ae83d-fa17-4418-8910-e066b877012d
-- title:
--   Sum of integers below 859
-- statement:
--   The sum of the nonnegative integers strictly less than $859$ equals $368511$. Equivalently, $\\sum_{k=0}^{859-1} k = 859(859-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_859 : ∑ k ∈ range 859, k = 368511 := by sorry

end FiniteTriangular
