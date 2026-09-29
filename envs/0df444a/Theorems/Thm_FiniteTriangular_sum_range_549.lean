-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_549
-- name    : FiniteTriangular.sum_range_549
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:30:43.381832+00:00
-- url     : https://prove2.me/theorems/62e9cb45-dd97-423a-9d3c-df08634a5a0a
-- title:
--   Sum of integers below 549
-- statement:
--   The sum of the nonnegative integers strictly less than $549$ equals $150426$. Equivalently, $\\sum_{k=0}^{549-1} k = 549(549-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_549 : ∑ k ∈ range 549, k = 150426 := by sorry

end FiniteTriangular
