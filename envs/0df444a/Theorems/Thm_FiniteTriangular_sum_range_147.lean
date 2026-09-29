-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_147
-- name    : FiniteTriangular.sum_range_147
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:58:10.964266+00:00
-- url     : https://prove2.me/theorems/5f2c1bef-7ee6-4970-a7ba-d085538836a6
-- title:
--   Sum of integers below 147
-- statement:
--   The sum of the nonnegative integers strictly less than $147$ equals $10731$. Equivalently, $\sum_{k=0}^{147-1} k = 147(147-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_147 : ∑ k ∈ range 147, k = 10731 := by sorry

end FiniteTriangular
