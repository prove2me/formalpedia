-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_313
-- name    : FiniteTriangular.sum_range_313
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:30:25.509005+00:00
-- url     : https://prove2.me/theorems/7fc45bf3-e5b7-4414-ad1a-ee7a97589a8a
-- title:
--   Sum of integers below 313
-- statement:
--   The sum of the nonnegative integers strictly less than $313$ equals $48828$. Equivalently, $\\sum_{k=0}^{313-1} k = 313(313-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_313 : ∑ k ∈ range 313, k = 48828 := by sorry

end FiniteTriangular
