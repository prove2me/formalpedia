-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_458
-- name    : FiniteTriangular.sum_range_458
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:11:47.030235+00:00
-- url     : https://prove2.me/theorems/f041fb3a-1c99-482d-8516-0b3ac5cf2bda
-- title:
--   Sum of integers below 458
-- statement:
--   The sum of the nonnegative integers strictly less than $458$ equals $104653$. Equivalently, $\\sum_{k=0}^{458-1} k = 458(458-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_458 : ∑ k ∈ range 458, k = 104653 := by sorry

end FiniteTriangular
