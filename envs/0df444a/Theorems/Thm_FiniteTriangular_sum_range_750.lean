-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_750
-- name    : FiniteTriangular.sum_range_750
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:16:20.985624+00:00
-- url     : https://prove2.me/theorems/d74aa601-378a-4338-ac2a-360cd1227caa
-- title:
--   Sum of integers below 750
-- statement:
--   The sum of the nonnegative integers strictly less than $750$ equals $280875$. Equivalently, $\\sum_{k=0}^{750-1} k = 750(750-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_750 : ∑ k ∈ range 750, k = 280875 := by sorry

end FiniteTriangular
