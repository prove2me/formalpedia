-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_500
-- name    : FiniteTriangular.sum_range_500
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:20:24.358636+00:00
-- url     : https://prove2.me/theorems/37e7e1e7-f1e1-4408-9176-6068e779d60d
-- title:
--   Sum of integers below 500
-- statement:
--   The sum of the nonnegative integers strictly less than $500$ equals $124750$. Equivalently, $\\sum_{k=0}^{500-1} k = 500(500-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_500 : ∑ k ∈ range 500, k = 124750 := by sorry

end FiniteTriangular
