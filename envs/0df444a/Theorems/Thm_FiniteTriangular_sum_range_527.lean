-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_527
-- name    : FiniteTriangular.sum_range_527
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:25:43.114865+00:00
-- url     : https://prove2.me/theorems/c69f4631-eed8-4dfa-9806-c67a2bf944f5
-- title:
--   Sum of integers below 527
-- statement:
--   The sum of the nonnegative integers strictly less than $527$ equals $138601$. Equivalently, $\\sum_{k=0}^{527-1} k = 527(527-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_527 : ∑ k ∈ range 527, k = 138601 := by sorry

end FiniteTriangular
