-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_276
-- name    : FiniteTriangular.sum_range_276
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:14:42.807189+00:00
-- url     : https://prove2.me/theorems/56659cde-9fac-497e-afde-dc1796bd2132
-- title:
--   Sum of integers below 276
-- statement:
--   The sum of the nonnegative integers strictly less than $276$ equals $37950$. Equivalently, $\\sum_{k=0}^{276-1} k = 276(276-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_276 : ∑ k ∈ range 276, k = 37950 := by sorry

end FiniteTriangular
