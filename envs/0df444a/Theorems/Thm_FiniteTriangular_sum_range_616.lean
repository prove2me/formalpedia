-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_616
-- name    : FiniteTriangular.sum_range_616
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:46:34.121671+00:00
-- url     : https://prove2.me/theorems/85b022ca-e32c-4925-926a-f4a7a95c2605
-- title:
--   Sum of integers below 616
-- statement:
--   The sum of the nonnegative integers strictly less than $616$ equals $189420$. Equivalently, $\\sum_{k=0}^{616-1} k = 616(616-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_616 : ∑ k ∈ range 616, k = 189420 := by sorry

end FiniteTriangular
