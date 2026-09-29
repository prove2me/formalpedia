-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_347
-- name    : FiniteTriangular.sum_range_347
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:37:36.827141+00:00
-- url     : https://prove2.me/theorems/dd761c7a-ee27-44f1-bb04-18b66e91e7fe
-- title:
--   Sum of integers below 347
-- statement:
--   The sum of the nonnegative integers strictly less than $347$ equals $60031$. Equivalently, $\\sum_{k=0}^{347-1} k = 347(347-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_347 : ∑ k ∈ range 347, k = 60031 := by sorry

end FiniteTriangular
