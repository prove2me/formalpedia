-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_973
-- name    : FiniteTriangular.sum_range_973
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:04:16.233459+00:00
-- url     : https://prove2.me/theorems/6ec2272a-3140-4287-9381-7f75614d1546
-- title:
--   Sum of integers below 973
-- statement:
--   The sum of the nonnegative integers strictly less than $973$ equals $472878$. Equivalently, $\\sum_{k=0}^{973-1} k = 973(973-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_973 : ∑ k ∈ range 973, k = 472878 := by sorry

end FiniteTriangular
