-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_528
-- name    : FiniteTriangular.sum_range_528
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:25:41.417621+00:00
-- url     : https://prove2.me/theorems/17ccded0-558e-48b3-9763-8dfefa2debd6
-- title:
--   Sum of integers below 528
-- statement:
--   The sum of the nonnegative integers strictly less than $528$ equals $139128$. Equivalently, $\\sum_{k=0}^{528-1} k = 528(528-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_528 : ∑ k ∈ range 528, k = 139128 := by sorry

end FiniteTriangular
