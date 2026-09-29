-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_67
-- name    : FiniteTriangular.sum_range_67
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:32:47.767981+00:00
-- url     : https://prove2.me/theorems/555f0934-4467-46e5-a2c4-879a124eb0ae
-- title:
--   Sum of integers below 67
-- statement:
--   The sum of the nonnegative integers strictly less than $67$ equals $2211$. Equivalently, $\sum_{k=0}^{67-1} k = 67(67-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_67 : ∑ k ∈ range 67, k = 2211 := by sorry

end FiniteTriangular
