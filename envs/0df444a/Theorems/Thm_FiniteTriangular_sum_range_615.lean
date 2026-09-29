-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_615
-- name    : FiniteTriangular.sum_range_615
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:46:32.020822+00:00
-- url     : https://prove2.me/theorems/a28cd37a-31f9-4e65-8ef5-5da84312d64d
-- title:
--   Sum of integers below 615
-- statement:
--   The sum of the nonnegative integers strictly less than $615$ equals $188805$. Equivalently, $\\sum_{k=0}^{615-1} k = 615(615-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_615 : ∑ k ∈ range 615, k = 188805 := by sorry

end FiniteTriangular
