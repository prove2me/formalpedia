-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_444
-- name    : FiniteTriangular.sum_range_444
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:08:01.66+00:00
-- url     : https://prove2.me/theorems/a0c16387-f975-4e3d-b83d-e48a8c06da59
-- title:
--   Sum of integers below 444
-- statement:
--   The sum of the nonnegative integers strictly less than $444$ equals $98346$. Equivalently, $\\sum_{k=0}^{444-1} k = 444(444-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_444 : ∑ k ∈ range 444, k = 98346 := by sorry

end FiniteTriangular
