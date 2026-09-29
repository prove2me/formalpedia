-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_737
-- name    : FiniteTriangular.sum_range_737
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:14:30.585264+00:00
-- url     : https://prove2.me/theorems/9403f6fc-c9c2-439d-98ca-85ce0878e471
-- title:
--   Sum of integers below 737
-- statement:
--   The sum of the nonnegative integers strictly less than $737$ equals $271216$. Equivalently, $\\sum_{k=0}^{737-1} k = 737(737-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_737 : ∑ k ∈ range 737, k = 271216 := by sorry

end FiniteTriangular
