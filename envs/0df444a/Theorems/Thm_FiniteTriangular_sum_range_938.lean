-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_938
-- name    : FiniteTriangular.sum_range_938
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:56:57.235914+00:00
-- url     : https://prove2.me/theorems/a855675a-ad7e-4514-ab37-fcf687d98a10
-- title:
--   Sum of integers below 938
-- statement:
--   The sum of the nonnegative integers strictly less than $938$ equals $439453$. Equivalently, $\\sum_{k=0}^{938-1} k = 938(938-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_938 : ∑ k ∈ range 938, k = 439453 := by sorry

end FiniteTriangular
