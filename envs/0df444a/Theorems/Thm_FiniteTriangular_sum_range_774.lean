-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_774
-- name    : FiniteTriangular.sum_range_774
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:21:25.430853+00:00
-- url     : https://prove2.me/theorems/6673401e-27ff-4d52-834b-2f745e8d2b24
-- title:
--   Sum of integers below 774
-- statement:
--   The sum of the nonnegative integers strictly less than $774$ equals $299151$. Equivalently, $\\sum_{k=0}^{774-1} k = 774(774-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_774 : ∑ k ∈ range 774, k = 299151 := by sorry

end FiniteTriangular
