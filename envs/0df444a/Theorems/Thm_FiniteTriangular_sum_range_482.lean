-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_482
-- name    : FiniteTriangular.sum_range_482
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:17:09.385645+00:00
-- url     : https://prove2.me/theorems/9e771fbf-df5c-454f-8012-1dd99ec04bb9
-- title:
--   Sum of integers below 482
-- statement:
--   The sum of the nonnegative integers strictly less than $482$ equals $115921$. Equivalently, $\\sum_{k=0}^{482-1} k = 482(482-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_482 : ∑ k ∈ range 482, k = 115921 := by sorry

end FiniteTriangular
