-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_734
-- name    : FiniteTriangular.sum_range_734
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:12:31.902731+00:00
-- url     : https://prove2.me/theorems/1b432711-ea57-4b02-8034-d343704c45c0
-- title:
--   Sum of integers below 734
-- statement:
--   The sum of the nonnegative integers strictly less than $734$ equals $269011$. Equivalently, $\\sum_{k=0}^{734-1} k = 734(734-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_734 : ∑ k ∈ range 734, k = 269011 := by sorry

end FiniteTriangular
