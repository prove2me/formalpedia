-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_107
-- name    : FiniteTriangular.sum_range_107
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:47:11.531841+00:00
-- url     : https://prove2.me/theorems/63fecd4a-10bc-4a26-92a6-2f17f29e1938
-- title:
--   Sum of integers below 107
-- statement:
--   The sum of the nonnegative integers strictly less than $107$ equals $5671$. Equivalently, $\sum_{k=0}^{107-1} k = 107(107-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_107 : ∑ k ∈ range 107, k = 5671 := by sorry

end FiniteTriangular
