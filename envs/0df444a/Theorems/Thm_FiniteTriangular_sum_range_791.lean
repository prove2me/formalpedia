-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_791
-- name    : FiniteTriangular.sum_range_791
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:24:54.330893+00:00
-- url     : https://prove2.me/theorems/76400e20-d76b-446f-8cb5-455d6923ef8d
-- title:
--   Sum of integers below 791
-- statement:
--   The sum of the nonnegative integers strictly less than $791$ equals $312445$. Equivalently, $\\sum_{k=0}^{791-1} k = 791(791-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_791 : ∑ k ∈ range 791, k = 312445 := by sorry

end FiniteTriangular
