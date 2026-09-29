-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_331
-- name    : FiniteTriangular.sum_range_331
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:34:05.928408+00:00
-- url     : https://prove2.me/theorems/0406040b-a116-4cc3-ad4a-1c4cb65a450f
-- title:
--   Sum of integers below 331
-- statement:
--   The sum of the nonnegative integers strictly less than $331$ equals $54615$. Equivalently, $\\sum_{k=0}^{331-1} k = 331(331-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_331 : ∑ k ∈ range 331, k = 54615 := by sorry

end FiniteTriangular
