-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_273
-- name    : FiniteTriangular.sum_range_273
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:14:42.119803+00:00
-- url     : https://prove2.me/theorems/adae0a3b-80fa-40b2-b93d-0dec060d60bb
-- title:
--   Sum of integers below 273
-- statement:
--   The sum of the nonnegative integers strictly less than $273$ equals $37128$. Equivalently, $\\sum_{k=0}^{273-1} k = 273(273-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_273 : ∑ k ∈ range 273, k = 37128 := by sorry

end FiniteTriangular
