-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_850
-- name    : FiniteTriangular.sum_range_850
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:38:22.793675+00:00
-- url     : https://prove2.me/theorems/ae7ad86c-87d0-4438-9bd6-63dc4e2d98fc
-- title:
--   Sum of integers below 850
-- statement:
--   The sum of the nonnegative integers strictly less than $850$ equals $360825$. Equivalently, $\\sum_{k=0}^{850-1} k = 850(850-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_850 : ∑ k ∈ range 850, k = 360825 := by sorry

end FiniteTriangular
