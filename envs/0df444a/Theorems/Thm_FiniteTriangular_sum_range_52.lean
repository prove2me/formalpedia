-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_52
-- name    : FiniteTriangular.sum_range_52
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:19:00.597981+00:00
-- url     : https://prove2.me/theorems/deefd129-d1cf-460b-b772-903d71c794a3
-- title:
--   Sum of integers below 52
-- statement:
--   The sum of the nonnegative integers strictly less than $52$ equals $1326$. Equivalently, $\sum_{k=0}^{52-1} k = 52(52-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_52 : ∑ k ∈ range 52, k = 1326 := by sorry

end FiniteTriangular
