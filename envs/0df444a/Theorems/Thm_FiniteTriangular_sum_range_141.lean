-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_141
-- name    : FiniteTriangular.sum_range_141
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:57:02.981296+00:00
-- url     : https://prove2.me/theorems/d1494fbf-221c-4cf5-bcb5-4a94cb6c98fd
-- title:
--   Sum of integers below 141
-- statement:
--   The sum of the nonnegative integers strictly less than $141$ equals $9870$. Equivalently, $\sum_{k=0}^{141-1} k = 141(141-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_141 : ∑ k ∈ range 141, k = 9870 := by sorry

end FiniteTriangular
