-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_88
-- name    : FiniteTriangular.sum_range_88
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:40:02.240918+00:00
-- url     : https://prove2.me/theorems/b4a5ef92-711a-4999-809b-c2d760724ccd
-- title:
--   Sum of integers below 88
-- statement:
--   The sum of the nonnegative integers strictly less than $88$ equals $3828$. Equivalently, $\sum_{k=0}^{88-1} k = 88(88-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_88 : ∑ k ∈ range 88, k = 3828 := by sorry

end FiniteTriangular
