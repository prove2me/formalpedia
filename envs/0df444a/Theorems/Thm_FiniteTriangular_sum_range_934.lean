-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_934
-- name    : FiniteTriangular.sum_range_934
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:55:10.581598+00:00
-- url     : https://prove2.me/theorems/2c9b8ec8-17b4-49f1-8da8-fc0dd78cd776
-- title:
--   Sum of integers below 934
-- statement:
--   The sum of the nonnegative integers strictly less than $934$ equals $435711$. Equivalently, $\\sum_{k=0}^{934-1} k = 934(934-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_934 : ∑ k ∈ range 934, k = 435711 := by sorry

end FiniteTriangular
