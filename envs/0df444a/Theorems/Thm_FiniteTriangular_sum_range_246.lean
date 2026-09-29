-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_246
-- name    : FiniteTriangular.sum_range_246
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:59:13.893294+00:00
-- url     : https://prove2.me/theorems/6f85e38e-b5b0-4972-9df3-116c4b9e42c3
-- title:
--   Sum of integers below 246
-- statement:
--   The sum of the nonnegative integers strictly less than $246$ equals $30135$. Equivalently, $\\sum_{k=0}^{246-1} k = 246(246-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_246 : ∑ k ∈ range 246, k = 30135 := by sorry

end FiniteTriangular
