-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_871
-- name    : FiniteTriangular.sum_range_871
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:41:48.843171+00:00
-- url     : https://prove2.me/theorems/ffa384d8-a83a-472f-8268-4d15e87b5849
-- title:
--   Sum of integers below 871
-- statement:
--   The sum of the nonnegative integers strictly less than $871$ equals $378885$. Equivalently, $\\sum_{k=0}^{871-1} k = 871(871-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_871 : ∑ k ∈ range 871, k = 378885 := by sorry

end FiniteTriangular
