-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_502
-- name    : FiniteTriangular.sum_range_502
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:20:25.213621+00:00
-- url     : https://prove2.me/theorems/ae22c3e3-5775-4b4c-8834-e97f7458cf95
-- title:
--   Sum of integers below 502
-- statement:
--   The sum of the nonnegative integers strictly less than $502$ equals $125751$. Equivalently, $\\sum_{k=0}^{502-1} k = 502(502-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_502 : ∑ k ∈ range 502, k = 125751 := by sorry

end FiniteTriangular
