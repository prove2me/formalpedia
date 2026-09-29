-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_785
-- name    : FiniteTriangular.sum_range_785
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:24:54.256975+00:00
-- url     : https://prove2.me/theorems/4b122ee0-2fa5-4304-b697-26a613667cf7
-- title:
--   Sum of integers below 785
-- statement:
--   The sum of the nonnegative integers strictly less than $785$ equals $307720$. Equivalently, $\\sum_{k=0}^{785-1} k = 785(785-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_785 : ∑ k ∈ range 785, k = 307720 := by sorry

end FiniteTriangular
