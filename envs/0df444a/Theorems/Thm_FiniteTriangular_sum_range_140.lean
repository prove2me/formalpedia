-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_140
-- name    : FiniteTriangular.sum_range_140
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:57:02.565745+00:00
-- url     : https://prove2.me/theorems/da70aa11-8e75-4e43-9d9b-006f7bbb1c2d
-- title:
--   Sum of integers below 140
-- statement:
--   The sum of the nonnegative integers strictly less than $140$ equals $9730$. Equivalently, $\sum_{k=0}^{140-1} k = 140(140-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_140 : ∑ k ∈ range 140, k = 9730 := by sorry

end FiniteTriangular
