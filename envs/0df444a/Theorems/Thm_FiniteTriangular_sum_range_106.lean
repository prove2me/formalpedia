-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_106
-- name    : FiniteTriangular.sum_range_106
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:47:11.079142+00:00
-- url     : https://prove2.me/theorems/367dd79a-675e-4ab7-8739-b67a39882f06
-- title:
--   Sum of integers below 106
-- statement:
--   The sum of the nonnegative integers strictly less than $106$ equals $5565$. Equivalently, $\sum_{k=0}^{106-1} k = 106(106-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_106 : ∑ k ∈ range 106, k = 5565 := by sorry

end FiniteTriangular
