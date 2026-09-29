-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_855
-- name    : FiniteTriangular.sum_range_855
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:38:21.177492+00:00
-- url     : https://prove2.me/theorems/56875ca0-3668-430f-8017-3ac36efccdba
-- title:
--   Sum of integers below 855
-- statement:
--   The sum of the nonnegative integers strictly less than $855$ equals $365085$. Equivalently, $\\sum_{k=0}^{855-1} k = 855(855-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_855 : ∑ k ∈ range 855, k = 365085 := by sorry

end FiniteTriangular
