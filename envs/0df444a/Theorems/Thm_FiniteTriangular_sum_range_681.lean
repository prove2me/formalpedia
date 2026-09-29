-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_681
-- name    : FiniteTriangular.sum_range_681
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:01:49.99758+00:00
-- url     : https://prove2.me/theorems/87033ee6-5c62-42be-99fa-d802aea3935a
-- title:
--   Sum of integers below 681
-- statement:
--   The sum of the nonnegative integers strictly less than $681$ equals $231540$. Equivalently, $\\sum_{k=0}^{681-1} k = 681(681-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_681 : ∑ k ∈ range 681, k = 231540 := by sorry

end FiniteTriangular
