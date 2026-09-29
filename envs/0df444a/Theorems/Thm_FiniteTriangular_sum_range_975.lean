-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_975
-- name    : FiniteTriangular.sum_range_975
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:04:12.486585+00:00
-- url     : https://prove2.me/theorems/61b254d5-25b4-42e5-8a2a-ee2337231be2
-- title:
--   Sum of integers below 975
-- statement:
--   The sum of the nonnegative integers strictly less than $975$ equals $474825$. Equivalently, $\\sum_{k=0}^{975-1} k = 975(975-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_975 : ∑ k ∈ range 975, k = 474825 := by sorry

end FiniteTriangular
