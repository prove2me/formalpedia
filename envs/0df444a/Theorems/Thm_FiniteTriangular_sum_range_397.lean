-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_397
-- name    : FiniteTriangular.sum_range_397
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:48:40.994226+00:00
-- url     : https://prove2.me/theorems/7461a9ce-974f-454e-adf0-f872cfe0d9c8
-- title:
--   Sum of integers below 397
-- statement:
--   The sum of the nonnegative integers strictly less than $397$ equals $78606$. Equivalently, $\\sum_{k=0}^{397-1} k = 397(397-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_397 : ∑ k ∈ range 397, k = 78606 := by sorry

end FiniteTriangular
