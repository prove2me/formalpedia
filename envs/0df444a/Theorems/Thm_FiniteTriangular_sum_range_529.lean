-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_529
-- name    : FiniteTriangular.sum_range_529
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:27:16.671357+00:00
-- url     : https://prove2.me/theorems/1c4606d2-386e-42e5-b25e-b1d43fc9a1ab
-- title:
--   Sum of integers below 529
-- statement:
--   The sum of the nonnegative integers strictly less than $529$ equals $139656$. Equivalently, $\\sum_{k=0}^{529-1} k = 529(529-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_529 : ∑ k ∈ range 529, k = 139656 := by sorry

end FiniteTriangular
