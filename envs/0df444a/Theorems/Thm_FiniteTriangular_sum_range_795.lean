-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_795
-- name    : FiniteTriangular.sum_range_795
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:26:34.481338+00:00
-- url     : https://prove2.me/theorems/cdcf5f45-e0d8-4f75-b4c3-5bde11d39c1e
-- title:
--   Sum of integers below 795
-- statement:
--   The sum of the nonnegative integers strictly less than $795$ equals $315615$. Equivalently, $\\sum_{k=0}^{795-1} k = 795(795-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_795 : ∑ k ∈ range 795, k = 315615 := by sorry

end FiniteTriangular
