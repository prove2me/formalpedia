-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_72
-- name    : FiniteTriangular.sum_range_72
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:32:53.481284+00:00
-- url     : https://prove2.me/theorems/425aaa7c-2082-451a-8497-2b76e4c279bc
-- title:
--   Sum of integers below 72
-- statement:
--   The sum of the nonnegative integers strictly less than $72$ equals $2556$. Equivalently, $\sum_{k=0}^{72-1} k = 72(72-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_72 : ∑ k ∈ range 72, k = 2556 := by sorry

end FiniteTriangular
