-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_629
-- name    : FiniteTriangular.sum_range_629
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:49:51.371667+00:00
-- url     : https://prove2.me/theorems/50e11b10-0550-4e13-9d85-f33bd2dd6340
-- title:
--   Sum of integers below 629
-- statement:
--   The sum of the nonnegative integers strictly less than $629$ equals $197506$. Equivalently, $\\sum_{k=0}^{629-1} k = 629(629-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_629 : ∑ k ∈ range 629, k = 197506 := by sorry

end FiniteTriangular
