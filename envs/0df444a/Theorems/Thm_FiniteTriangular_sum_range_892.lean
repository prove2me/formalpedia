-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_892
-- name    : FiniteTriangular.sum_range_892
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:46:54.95523+00:00
-- url     : https://prove2.me/theorems/d740ba31-856a-44ce-9505-936d6336b8f1
-- title:
--   Sum of integers below 892
-- statement:
--   The sum of the nonnegative integers strictly less than $892$ equals $397386$. Equivalently, $\\sum_{k=0}^{892-1} k = 892(892-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_892 : ∑ k ∈ range 892, k = 397386 := by sorry

end FiniteTriangular
