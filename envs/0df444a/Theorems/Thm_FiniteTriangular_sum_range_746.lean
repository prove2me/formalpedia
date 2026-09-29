-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_746
-- name    : FiniteTriangular.sum_range_746
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:16:19.581236+00:00
-- url     : https://prove2.me/theorems/74c1491c-6ba9-4617-a9ab-dbbb46b48c00
-- title:
--   Sum of integers below 746
-- statement:
--   The sum of the nonnegative integers strictly less than $746$ equals $277885$. Equivalently, $\\sum_{k=0}^{746-1} k = 746(746-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_746 : ∑ k ∈ range 746, k = 277885 := by sorry

end FiniteTriangular
