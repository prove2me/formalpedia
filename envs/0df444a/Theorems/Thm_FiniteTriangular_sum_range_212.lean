-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_212
-- name    : FiniteTriangular.sum_range_212
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:51:33.783357+00:00
-- url     : https://prove2.me/theorems/04b292e9-7233-4d9c-acab-4b8bbc86ec15
-- title:
--   Sum of integers below 212
-- statement:
--   The sum of the nonnegative integers strictly less than $212$ equals $22366$. Equivalently, $\\sum_{k=0}^{212-1} k = 212(212-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_212 : ∑ k ∈ range 212, k = 22366 := by sorry

end FiniteTriangular
