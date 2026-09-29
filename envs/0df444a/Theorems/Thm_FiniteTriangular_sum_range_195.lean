-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_195
-- name    : FiniteTriangular.sum_range_195
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:47:20.71945+00:00
-- url     : https://prove2.me/theorems/aa4494e5-7524-4e6b-865e-221abc7597f5
-- title:
--   Sum of integers below 195
-- statement:
--   The sum of the nonnegative integers strictly less than $195$ equals $18915$. Equivalently, $\\sum_{k=0}^{195-1} k = 195(195-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_195 : ∑ k ∈ range 195, k = 18915 := by sorry

end FiniteTriangular
