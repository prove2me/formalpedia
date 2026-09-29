-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_741
-- name    : FiniteTriangular.sum_range_741
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:14:33.269423+00:00
-- url     : https://prove2.me/theorems/a8aafe51-319c-49cf-bf21-6ff3b1cae442
-- title:
--   Sum of integers below 741
-- statement:
--   The sum of the nonnegative integers strictly less than $741$ equals $274170$. Equivalently, $\\sum_{k=0}^{741-1} k = 741(741-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_741 : ∑ k ∈ range 741, k = 274170 := by sorry

end FiniteTriangular
