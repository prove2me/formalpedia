-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_109
-- name    : FiniteTriangular.sum_range_109
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:47:10.498495+00:00
-- url     : https://prove2.me/theorems/4da751d8-3c28-4b4d-868e-00ee8011b7dd
-- title:
--   Sum of integers below 109
-- statement:
--   The sum of the nonnegative integers strictly less than $109$ equals $5886$. Equivalently, $\sum_{k=0}^{109-1} k = 109(109-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_109 : ∑ k ∈ range 109, k = 5886 := by sorry

end FiniteTriangular
