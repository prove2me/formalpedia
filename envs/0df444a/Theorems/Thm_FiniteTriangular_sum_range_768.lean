-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_768
-- name    : FiniteTriangular.sum_range_768
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:19:36.590923+00:00
-- url     : https://prove2.me/theorems/9b73f3c6-9358-4614-99f8-46a9ceed4c46
-- title:
--   Sum of integers below 768
-- statement:
--   The sum of the nonnegative integers strictly less than $768$ equals $294528$. Equivalently, $\\sum_{k=0}^{768-1} k = 768(768-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_768 : ∑ k ∈ range 768, k = 294528 := by sorry

end FiniteTriangular
