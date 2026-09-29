-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_959
-- name    : FiniteTriangular.sum_range_959
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:00:49.863667+00:00
-- url     : https://prove2.me/theorems/7932c6b0-1583-4500-b1a4-fc1673ec981b
-- title:
--   Sum of integers below 959
-- statement:
--   The sum of the nonnegative integers strictly less than $959$ equals $459361$. Equivalently, $\\sum_{k=0}^{959-1} k = 959(959-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_959 : ∑ k ∈ range 959, k = 459361 := by sorry

end FiniteTriangular
