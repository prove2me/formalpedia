-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_318
-- name    : FiniteTriangular.sum_range_318
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:30:27.445137+00:00
-- url     : https://prove2.me/theorems/349bd435-d342-41f8-8a3b-506c20fec401
-- title:
--   Sum of integers below 318
-- statement:
--   The sum of the nonnegative integers strictly less than $318$ equals $50403$. Equivalently, $\\sum_{k=0}^{318-1} k = 318(318-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_318 : ∑ k ∈ range 318, k = 50403 := by sorry

end FiniteTriangular
