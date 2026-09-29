-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_237
-- name    : FiniteTriangular.sum_range_237
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:57:36.746727+00:00
-- url     : https://prove2.me/theorems/a6597dbd-d72e-4642-847c-39cefc0b71d9
-- title:
--   Sum of integers below 237
-- statement:
--   The sum of the nonnegative integers strictly less than $237$ equals $27966$. Equivalently, $\\sum_{k=0}^{237-1} k = 237(237-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_237 : ∑ k ∈ range 237, k = 27966 := by sorry

end FiniteTriangular
