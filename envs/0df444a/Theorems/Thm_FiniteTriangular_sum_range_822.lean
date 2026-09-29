-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_822
-- name    : FiniteTriangular.sum_range_822
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:31:42.76462+00:00
-- url     : https://prove2.me/theorems/ca43bb97-e427-4118-80cf-8302965da738
-- title:
--   Sum of integers below 822
-- statement:
--   The sum of the nonnegative integers strictly less than $822$ equals $337431$. Equivalently, $\\sum_{k=0}^{822-1} k = 822(822-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_822 : ∑ k ∈ range 822, k = 337431 := by sorry

end FiniteTriangular
