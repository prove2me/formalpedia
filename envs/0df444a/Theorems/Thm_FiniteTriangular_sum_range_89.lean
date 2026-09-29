-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_89
-- name    : FiniteTriangular.sum_range_89
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:43:40.643004+00:00
-- url     : https://prove2.me/theorems/432155d1-01ea-41c6-b482-7ee75330dad7
-- title:
--   Sum of integers below 89
-- statement:
--   The sum of the nonnegative integers strictly less than $89$ equals $3916$. Equivalently, $\sum_{k=0}^{89-1} k = 89(89-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_89 : ∑ k ∈ range 89, k = 3916 := by sorry

end FiniteTriangular
