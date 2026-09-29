-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_364
-- name    : FiniteTriangular.sum_range_364
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:41:15.898381+00:00
-- url     : https://prove2.me/theorems/33eb12a9-b355-4d61-ae5c-fd688d763d43
-- title:
--   Sum of integers below 364
-- statement:
--   The sum of the nonnegative integers strictly less than $364$ equals $66066$. Equivalently, $\\sum_{k=0}^{364-1} k = 364(364-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_364 : ∑ k ∈ range 364, k = 66066 := by sorry

end FiniteTriangular
