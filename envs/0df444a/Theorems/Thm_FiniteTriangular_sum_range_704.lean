-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_704
-- name    : FiniteTriangular.sum_range_704
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:04:59.157193+00:00
-- url     : https://prove2.me/theorems/f3d033a9-14a0-4cc7-a943-db58998bcdcf
-- title:
--   Sum of integers below 704
-- statement:
--   The sum of the nonnegative integers strictly less than $704$ equals $247456$. Equivalently, $\\sum_{k=0}^{704-1} k = 704(704-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_704 : ∑ k ∈ range 704, k = 247456 := by sorry

end FiniteTriangular
