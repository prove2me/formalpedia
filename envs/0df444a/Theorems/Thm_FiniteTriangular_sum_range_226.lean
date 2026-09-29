-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_226
-- name    : FiniteTriangular.sum_range_226
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:55:00.511768+00:00
-- url     : https://prove2.me/theorems/1a69607e-3027-45b0-ac5f-4e4d0ea22b91
-- title:
--   Sum of integers below 226
-- statement:
--   The sum of the nonnegative integers strictly less than $226$ equals $25425$. Equivalently, $\\sum_{k=0}^{226-1} k = 226(226-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_226 : ∑ k ∈ range 226, k = 25425 := by sorry

end FiniteTriangular
