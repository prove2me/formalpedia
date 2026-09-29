-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_152
-- name    : FiniteTriangular.sum_range_152
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:58:16.954893+00:00
-- url     : https://prove2.me/theorems/e76538d4-1958-44b5-a306-b5ffc604fdf2
-- title:
--   Sum of integers below 152
-- statement:
--   The sum of the nonnegative integers strictly less than $152$ equals $11476$. Equivalently, $\sum_{k=0}^{152-1} k = 152(152-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_152 : ∑ k ∈ range 152, k = 11476 := by sorry

end FiniteTriangular
