-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_909
-- name    : FiniteTriangular.sum_range_909
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:50:10.86641+00:00
-- url     : https://prove2.me/theorems/4eee2401-2b24-4e55-91b6-eb0d45fc9bf3
-- title:
--   Sum of integers below 909
-- statement:
--   The sum of the nonnegative integers strictly less than $909$ equals $412686$. Equivalently, $\\sum_{k=0}^{909-1} k = 909(909-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_909 : ∑ k ∈ range 909, k = 412686 := by sorry

end FiniteTriangular
