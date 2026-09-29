-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_740
-- name    : FiniteTriangular.sum_range_740
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:14:31.609105+00:00
-- url     : https://prove2.me/theorems/13d9cb27-017c-436f-a53b-e4790572a1ab
-- title:
--   Sum of integers below 740
-- statement:
--   The sum of the nonnegative integers strictly less than $740$ equals $273430$. Equivalently, $\\sum_{k=0}^{740-1} k = 740(740-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_740 : ∑ k ∈ range 740, k = 273430 := by sorry

end FiniteTriangular
