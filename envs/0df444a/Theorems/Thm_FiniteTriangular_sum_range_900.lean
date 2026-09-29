-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_900
-- name    : FiniteTriangular.sum_range_900
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:48:33.760089+00:00
-- url     : https://prove2.me/theorems/681b262d-9c44-4c76-a707-fff17a334c5a
-- title:
--   Sum of integers below 900
-- statement:
--   The sum of the nonnegative integers strictly less than $900$ equals $404550$. Equivalently, $\\sum_{k=0}^{900-1} k = 900(900-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_900 : ∑ k ∈ range 900, k = 404550 := by sorry

end FiniteTriangular
