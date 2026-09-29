-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_317
-- name    : FiniteTriangular.sum_range_317
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:30:27.55788+00:00
-- url     : https://prove2.me/theorems/28678e25-b7b1-4084-9a00-842535c729e7
-- title:
--   Sum of integers below 317
-- statement:
--   The sum of the nonnegative integers strictly less than $317$ equals $50086$. Equivalently, $\\sum_{k=0}^{317-1} k = 317(317-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_317 : ∑ k ∈ range 317, k = 50086 := by sorry

end FiniteTriangular
