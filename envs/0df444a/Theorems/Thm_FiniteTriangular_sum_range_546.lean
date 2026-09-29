-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_546
-- name    : FiniteTriangular.sum_range_546
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:30:46.508643+00:00
-- url     : https://prove2.me/theorems/ed439d10-4590-4d1e-a98d-74673c28d84b
-- title:
--   Sum of integers below 546
-- statement:
--   The sum of the nonnegative integers strictly less than $546$ equals $148785$. Equivalently, $\\sum_{k=0}^{546-1} k = 546(546-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_546 : ∑ k ∈ range 546, k = 148785 := by sorry

end FiniteTriangular
