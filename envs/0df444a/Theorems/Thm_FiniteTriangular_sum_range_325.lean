-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_325
-- name    : FiniteTriangular.sum_range_325
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:32:11.780863+00:00
-- url     : https://prove2.me/theorems/624d86e3-5a64-4557-8011-832f8c7ecb7a
-- title:
--   Sum of integers below 325
-- statement:
--   The sum of the nonnegative integers strictly less than $325$ equals $52650$. Equivalently, $\\sum_{k=0}^{325-1} k = 325(325-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_325 : ∑ k ∈ range 325, k = 52650 := by sorry

end FiniteTriangular
