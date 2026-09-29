-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_919
-- name    : FiniteTriangular.sum_range_919
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:51:46.576959+00:00
-- url     : https://prove2.me/theorems/ea1a2ff1-d856-4eea-9d0b-3eab7ad56f23
-- title:
--   Sum of integers below 919
-- statement:
--   The sum of the nonnegative integers strictly less than $919$ equals $421821$. Equivalently, $\\sum_{k=0}^{919-1} k = 919(919-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_919 : ∑ k ∈ range 919, k = 421821 := by sorry

end FiniteTriangular
