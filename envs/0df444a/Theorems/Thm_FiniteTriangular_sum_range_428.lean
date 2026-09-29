-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_428
-- name    : FiniteTriangular.sum_range_428
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:55:41.100468+00:00
-- url     : https://prove2.me/theorems/1dcb21cd-386f-4e81-8d84-231f8659a72f
-- title:
--   Sum of integers below 428
-- statement:
--   The sum of the nonnegative integers strictly less than $428$ equals $91378$. Equivalently, $\\sum_{k=0}^{428-1} k = 428(428-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_428 : ∑ k ∈ range 428, k = 91378 := by sorry

end FiniteTriangular
