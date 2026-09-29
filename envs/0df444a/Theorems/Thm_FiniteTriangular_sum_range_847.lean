-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_847
-- name    : FiniteTriangular.sum_range_847
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:36:45.147463+00:00
-- url     : https://prove2.me/theorems/59270fb9-0449-4df5-ab76-fecb57574325
-- title:
--   Sum of integers below 847
-- statement:
--   The sum of the nonnegative integers strictly less than $847$ equals $358281$. Equivalently, $\\sum_{k=0}^{847-1} k = 847(847-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_847 : ∑ k ∈ range 847, k = 358281 := by sorry

end FiniteTriangular
