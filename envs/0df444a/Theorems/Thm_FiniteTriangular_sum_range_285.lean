-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_285
-- name    : FiniteTriangular.sum_range_285
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:16:28.765347+00:00
-- url     : https://prove2.me/theorems/30eef9b4-6c74-4d61-97e2-ef15b4f7712e
-- title:
--   Sum of integers below 285
-- statement:
--   The sum of the nonnegative integers strictly less than $285$ equals $40470$. Equivalently, $\\sum_{k=0}^{285-1} k = 285(285-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_285 : ∑ k ∈ range 285, k = 40470 := by sorry

end FiniteTriangular
