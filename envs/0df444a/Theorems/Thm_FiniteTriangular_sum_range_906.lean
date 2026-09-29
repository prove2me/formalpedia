-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_906
-- name    : FiniteTriangular.sum_range_906
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:50:12.202805+00:00
-- url     : https://prove2.me/theorems/0ca94f03-4680-4d22-95be-a4fb20f07a68
-- title:
--   Sum of integers below 906
-- statement:
--   The sum of the nonnegative integers strictly less than $906$ equals $409965$. Equivalently, $\\sum_{k=0}^{906-1} k = 906(906-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_906 : ∑ k ∈ range 906, k = 409965 := by sorry

end FiniteTriangular
