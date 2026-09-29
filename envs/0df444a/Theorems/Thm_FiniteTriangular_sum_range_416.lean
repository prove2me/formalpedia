-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_416
-- name    : FiniteTriangular.sum_range_416
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:52:10.190719+00:00
-- url     : https://prove2.me/theorems/96a934e5-b7a0-4d4c-9fbe-e50341a6d4b6
-- title:
--   Sum of integers below 416
-- statement:
--   The sum of the nonnegative integers strictly less than $416$ equals $86320$. Equivalently, $\\sum_{k=0}^{416-1} k = 416(416-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_416 : ∑ k ∈ range 416, k = 86320 := by sorry

end FiniteTriangular
