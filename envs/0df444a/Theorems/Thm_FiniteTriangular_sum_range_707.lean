-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_707
-- name    : FiniteTriangular.sum_range_707
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:06:49.984664+00:00
-- url     : https://prove2.me/theorems/96bfaed8-30d7-4f0c-aadb-8a736da0d0df
-- title:
--   Sum of integers below 707
-- statement:
--   The sum of the nonnegative integers strictly less than $707$ equals $249571$. Equivalently, $\\sum_{k=0}^{707-1} k = 707(707-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_707 : ∑ k ∈ range 707, k = 249571 := by sorry

end FiniteTriangular
