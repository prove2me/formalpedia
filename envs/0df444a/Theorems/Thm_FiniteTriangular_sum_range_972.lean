-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_972
-- name    : FiniteTriangular.sum_range_972
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:04:15.22583+00:00
-- url     : https://prove2.me/theorems/93e6ab85-05ec-4249-a2b5-f3e81b0546bf
-- title:
--   Sum of integers below 972
-- statement:
--   The sum of the nonnegative integers strictly less than $972$ equals $471906$. Equivalently, $\\sum_{k=0}^{972-1} k = 972(972-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_972 : ∑ k ∈ range 972, k = 471906 := by sorry

end FiniteTriangular
