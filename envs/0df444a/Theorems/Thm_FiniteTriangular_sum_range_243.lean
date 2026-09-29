-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_243
-- name    : FiniteTriangular.sum_range_243
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:59:17.288634+00:00
-- url     : https://prove2.me/theorems/89806104-8413-485c-9b0d-8686d38035f3
-- title:
--   Sum of integers below 243
-- statement:
--   The sum of the nonnegative integers strictly less than $243$ equals $29403$. Equivalently, $\\sum_{k=0}^{243-1} k = 243(243-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_243 : ∑ k ∈ range 243, k = 29403 := by sorry

end FiniteTriangular
