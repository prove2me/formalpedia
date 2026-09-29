-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_827
-- name    : FiniteTriangular.sum_range_827
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:33:30.63631+00:00
-- url     : https://prove2.me/theorems/0fa79788-60cc-4efb-a32f-c077dd2aa8d1
-- title:
--   Sum of integers below 827
-- statement:
--   The sum of the nonnegative integers strictly less than $827$ equals $341551$. Equivalently, $\\sum_{k=0}^{827-1} k = 827(827-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_827 : ∑ k ∈ range 827, k = 341551 := by sorry

end FiniteTriangular
