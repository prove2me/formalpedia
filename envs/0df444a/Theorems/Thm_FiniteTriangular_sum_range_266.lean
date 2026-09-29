-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_266
-- name    : FiniteTriangular.sum_range_266
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:12:49.76042+00:00
-- url     : https://prove2.me/theorems/e5b28b46-24b8-46ba-bd84-0cdedb2d4d27
-- title:
--   Sum of integers below 266
-- statement:
--   The sum of the nonnegative integers strictly less than $266$ equals $35245$. Equivalently, $\\sum_{k=0}^{266-1} k = 266(266-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_266 : ∑ k ∈ range 266, k = 35245 := by sorry

end FiniteTriangular
