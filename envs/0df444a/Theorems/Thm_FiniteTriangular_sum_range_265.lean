-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_265
-- name    : FiniteTriangular.sum_range_265
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:12:46.22437+00:00
-- url     : https://prove2.me/theorems/f3824a20-c373-4e29-82cd-427b94845cfd
-- title:
--   Sum of integers below 265
-- statement:
--   The sum of the nonnegative integers strictly less than $265$ equals $34980$. Equivalently, $\\sum_{k=0}^{265-1} k = 265(265-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_265 : ∑ k ∈ range 265, k = 34980 := by sorry

end FiniteTriangular
