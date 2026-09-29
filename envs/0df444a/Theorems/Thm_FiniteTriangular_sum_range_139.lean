-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_139
-- name    : FiniteTriangular.sum_range_139
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:57:03.252967+00:00
-- url     : https://prove2.me/theorems/809ff3d9-ebc3-4166-9d81-0697d1cecd4b
-- title:
--   Sum of integers below 139
-- statement:
--   The sum of the nonnegative integers strictly less than $139$ equals $9591$. Equivalently, $\sum_{k=0}^{139-1} k = 139(139-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_139 : ∑ k ∈ range 139, k = 9591 := by sorry

end FiniteTriangular
