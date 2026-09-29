-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_562
-- name    : FiniteTriangular.sum_range_562
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:36:04.607021+00:00
-- url     : https://prove2.me/theorems/5d92bc76-9eb2-4531-b98c-4e4d6ab3223a
-- title:
--   Sum of integers below 562
-- statement:
--   The sum of the nonnegative integers strictly less than $562$ equals $157641$. Equivalently, $\\sum_{k=0}^{562-1} k = 562(562-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_562 : ∑ k ∈ range 562, k = 157641 := by sorry

end FiniteTriangular
