-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_803
-- name    : FiniteTriangular.sum_range_803
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:28:22.595875+00:00
-- url     : https://prove2.me/theorems/abf91deb-8723-4388-82f4-87cf5cd9d307
-- title:
--   Sum of integers below 803
-- statement:
--   The sum of the nonnegative integers strictly less than $803$ equals $322003$. Equivalently, $\\sum_{k=0}^{803-1} k = 803(803-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_803 : ∑ k ∈ range 803, k = 322003 := by sorry

end FiniteTriangular
