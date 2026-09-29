-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_105
-- name    : FiniteTriangular.sum_range_105
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:47:09.388988+00:00
-- url     : https://prove2.me/theorems/a20fa042-32a7-400f-96af-15e5bb765ffe
-- title:
--   Sum of integers below 105
-- statement:
--   The sum of the nonnegative integers strictly less than $105$ equals $5460$. Equivalently, $\sum_{k=0}^{105-1} k = 105(105-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_105 : ∑ k ∈ range 105, k = 5460 := by sorry

end FiniteTriangular
