-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_77
-- name    : FiniteTriangular.sum_range_77
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:38:11.133528+00:00
-- url     : https://prove2.me/theorems/e8eb3e72-3a98-408e-ae8a-320507bf12b4
-- title:
--   Sum of integers below 77
-- statement:
--   The sum of the nonnegative integers strictly less than $77$ equals $2926$. Equivalently, $\sum_{k=0}^{77-1} k = 77(77-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_77 : ∑ k ∈ range 77, k = 2926 := by sorry

end FiniteTriangular
