-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_463
-- name    : FiniteTriangular.sum_range_463
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:11:46.121585+00:00
-- url     : https://prove2.me/theorems/139a358a-9c98-4124-82fb-34f11bdfbbbd
-- title:
--   Sum of integers below 463
-- statement:
--   The sum of the nonnegative integers strictly less than $463$ equals $106953$. Equivalently, $\\sum_{k=0}^{463-1} k = 463(463-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_463 : ∑ k ∈ range 463, k = 106953 := by sorry

end FiniteTriangular
