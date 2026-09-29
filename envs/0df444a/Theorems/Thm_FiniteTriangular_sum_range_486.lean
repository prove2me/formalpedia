-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_486
-- name    : FiniteTriangular.sum_range_486
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:17:12.357762+00:00
-- url     : https://prove2.me/theorems/05e421f7-cd2c-4df8-ae76-681e48944adc
-- title:
--   Sum of integers below 486
-- statement:
--   The sum of the nonnegative integers strictly less than $486$ equals $117855$. Equivalently, $\\sum_{k=0}^{486-1} k = 486(486-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_486 : ∑ k ∈ range 486, k = 117855 := by sorry

end FiniteTriangular
