-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_352
-- name    : FiniteTriangular.sum_range_352
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:37:39.979043+00:00
-- url     : https://prove2.me/theorems/86870034-7b49-45d7-9f1a-b84202c86de4
-- title:
--   Sum of integers below 352
-- statement:
--   The sum of the nonnegative integers strictly less than $352$ equals $61776$. Equivalently, $\\sum_{k=0}^{352-1} k = 352(352-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_352 : ∑ k ∈ range 352, k = 61776 := by sorry

end FiniteTriangular
