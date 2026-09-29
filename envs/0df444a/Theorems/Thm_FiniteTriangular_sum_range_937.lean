-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_937
-- name    : FiniteTriangular.sum_range_937
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:56:57.178231+00:00
-- url     : https://prove2.me/theorems/fd22be0f-1fe1-4203-bec2-216998549442
-- title:
--   Sum of integers below 937
-- statement:
--   The sum of the nonnegative integers strictly less than $937$ equals $438516$. Equivalently, $\\sum_{k=0}^{937-1} k = 937(937-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_937 : ∑ k ∈ range 937, k = 438516 := by sorry

end FiniteTriangular
