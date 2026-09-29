-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_24
-- name    : FiniteTriangular.sum_range_24
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:08:25.116118+00:00
-- url     : https://prove2.me/theorems/d81fcaf0-8c04-4b20-b16d-97e4c979a58b
-- title:
--   Sum of integers below 24
-- statement:
--   The sum of the nonnegative integers strictly less than $24$ equals $276$. Equivalently, $\sum_{k=0}^{24-1} k = 24(24-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_24 : ∑ k ∈ range 24, k = 276 := by sorry

end FiniteTriangular
