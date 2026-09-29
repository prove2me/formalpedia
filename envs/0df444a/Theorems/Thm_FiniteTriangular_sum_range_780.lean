-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_780
-- name    : FiniteTriangular.sum_range_780
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:23:09.912258+00:00
-- url     : https://prove2.me/theorems/75ea8b43-e05b-41b4-a5ce-1987e28ecc35
-- title:
--   Sum of integers below 780
-- statement:
--   The sum of the nonnegative integers strictly less than $780$ equals $303810$. Equivalently, $\\sum_{k=0}^{780-1} k = 780(780-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_780 : ∑ k ∈ range 780, k = 303810 := by sorry

end FiniteTriangular
