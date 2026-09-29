-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_504
-- name    : FiniteTriangular.sum_range_504
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:20:27.007577+00:00
-- url     : https://prove2.me/theorems/8da707b0-c905-49ee-9b35-779616a356be
-- title:
--   Sum of integers below 504
-- statement:
--   The sum of the nonnegative integers strictly less than $504$ equals $126756$. Equivalently, $\\sum_{k=0}^{504-1} k = 504(504-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_504 : ∑ k ∈ range 504, k = 126756 := by sorry

end FiniteTriangular
