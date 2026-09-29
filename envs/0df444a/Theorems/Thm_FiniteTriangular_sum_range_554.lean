-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_554
-- name    : FiniteTriangular.sum_range_554
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:13.873725+00:00
-- url     : https://prove2.me/theorems/e158c462-be8f-4596-b976-2bfdb984334b
-- title:
--   Sum of integers below 554
-- statement:
--   The sum of the nonnegative integers strictly less than $554$ equals $153181$. Equivalently, $\\sum_{k=0}^{554-1} k = 554(554-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_554 : ∑ k ∈ range 554, k = 153181 := by sorry

end FiniteTriangular
