-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_121
-- name    : FiniteTriangular.sum_range_121
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:54:07.36148+00:00
-- url     : https://prove2.me/theorems/132432ce-41f6-4b62-ac89-676bc6959cee
-- title:
--   Sum of integers below 121
-- statement:
--   The sum of the nonnegative integers strictly less than $121$ equals $7260$. Equivalently, $\sum_{k=0}^{121-1} k = 121(121-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_121 : ∑ k ∈ range 121, k = 7260 := by sorry

end FiniteTriangular
