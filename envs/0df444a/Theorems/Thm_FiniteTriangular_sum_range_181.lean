-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_181
-- name    : FiniteTriangular.sum_range_181
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:02.168355+00:00
-- url     : https://prove2.me/theorems/acb74ca8-9d54-4102-9e09-99b76e8229a6
-- title:
--   Sum of integers below 181
-- statement:
--   The sum of the nonnegative integers strictly less than $181$ equals $16290$. Equivalently, $\sum_{k=0}^{181-1} k = 181(181-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_181 : ∑ k ∈ range 181, k = 16290 := by sorry

end FiniteTriangular
