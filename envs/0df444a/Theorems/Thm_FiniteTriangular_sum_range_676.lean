-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_676
-- name    : FiniteTriangular.sum_range_676
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:59:59.616371+00:00
-- url     : https://prove2.me/theorems/4a1d6cd3-9c72-4702-85ba-06dfdeb8fa78
-- title:
--   Sum of integers below 676
-- statement:
--   The sum of the nonnegative integers strictly less than $676$ equals $228150$. Equivalently, $\\sum_{k=0}^{676-1} k = 676(676-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_676 : ∑ k ∈ range 676, k = 228150 := by sorry

end FiniteTriangular
