-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_122
-- name    : FiniteTriangular.sum_range_122
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:54:06.689608+00:00
-- url     : https://prove2.me/theorems/5ad8a4de-b84f-4594-b006-bb03226eedfb
-- title:
--   Sum of integers below 122
-- statement:
--   The sum of the nonnegative integers strictly less than $122$ equals $7381$. Equivalently, $\sum_{k=0}^{122-1} k = 122(122-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_122 : ∑ k ∈ range 122, k = 7381 := by sorry

end FiniteTriangular
