-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_722
-- name    : FiniteTriangular.sum_range_722
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:10:48.92199+00:00
-- url     : https://prove2.me/theorems/ff4250ed-3fd0-4db9-93bd-62124bea6ee8
-- title:
--   Sum of integers below 722
-- statement:
--   The sum of the nonnegative integers strictly less than $722$ equals $260281$. Equivalently, $\\sum_{k=0}^{722-1} k = 722(722-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_722 : ∑ k ∈ range 722, k = 260281 := by sorry

end FiniteTriangular
