-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_238
-- name    : FiniteTriangular.sum_range_238
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:57:33.435258+00:00
-- url     : https://prove2.me/theorems/0152da58-2751-4239-a4fe-9270ee0d4e5b
-- title:
--   Sum of integers below 238
-- statement:
--   The sum of the nonnegative integers strictly less than $238$ equals $28203$. Equivalently, $\\sum_{k=0}^{238-1} k = 238(238-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_238 : ∑ k ∈ range 238, k = 28203 := by sorry

end FiniteTriangular
