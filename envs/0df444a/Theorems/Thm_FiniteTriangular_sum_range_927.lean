-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_927
-- name    : FiniteTriangular.sum_range_927
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:53:35.468279+00:00
-- url     : https://prove2.me/theorems/5a79c20d-9fcb-431e-a6f8-70d259cb03ed
-- title:
--   Sum of integers below 927
-- statement:
--   The sum of the nonnegative integers strictly less than $927$ equals $429201$. Equivalently, $\\sum_{k=0}^{927-1} k = 927(927-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_927 : ∑ k ∈ range 927, k = 429201 := by sorry

end FiniteTriangular
