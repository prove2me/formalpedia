-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_230
-- name    : FiniteTriangular.sum_range_230
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:55:02.134446+00:00
-- url     : https://prove2.me/theorems/3480ab55-dc2c-4688-a3c2-78000e883f8a
-- title:
--   Sum of integers below 230
-- statement:
--   The sum of the nonnegative integers strictly less than $230$ equals $26335$. Equivalently, $\\sum_{k=0}^{230-1} k = 230(230-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_230 : ∑ k ∈ range 230, k = 26335 := by sorry

end FiniteTriangular
