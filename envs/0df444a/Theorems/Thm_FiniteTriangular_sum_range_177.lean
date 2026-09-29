-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_177
-- name    : FiniteTriangular.sum_range_177
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:01.029463+00:00
-- url     : https://prove2.me/theorems/f74a3758-2364-49c1-a34f-d7bda42f9d23
-- title:
--   Sum of integers below 177
-- statement:
--   The sum of the nonnegative integers strictly less than $177$ equals $15576$. Equivalently, $\sum_{k=0}^{177-1} k = 177(177-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_177 : ∑ k ∈ range 177, k = 15576 := by sorry

end FiniteTriangular
