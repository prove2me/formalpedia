-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_124
-- name    : FiniteTriangular.sum_range_124
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:54:02.744882+00:00
-- url     : https://prove2.me/theorems/95b342c0-e050-4ba9-84b0-c68c3e8daffb
-- title:
--   Sum of integers below 124
-- statement:
--   The sum of the nonnegative integers strictly less than $124$ equals $7626$. Equivalently, $\sum_{k=0}^{124-1} k = 124(124-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_124 : ∑ k ∈ range 124, k = 7626 := by sorry

end FiniteTriangular
