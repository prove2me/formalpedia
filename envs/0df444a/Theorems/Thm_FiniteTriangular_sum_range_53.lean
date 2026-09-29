-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_53
-- name    : FiniteTriangular.sum_range_53
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:19:02.117732+00:00
-- url     : https://prove2.me/theorems/5d588505-1e55-4f98-a56f-8618dbf4a4a1
-- title:
--   Sum of integers below 53
-- statement:
--   The sum of the nonnegative integers strictly less than $53$ equals $1378$. Equivalently, $\sum_{k=0}^{53-1} k = 53(53-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_53 : ∑ k ∈ range 53, k = 1378 := by sorry

end FiniteTriangular
