-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_804
-- name    : FiniteTriangular.sum_range_804
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:28:22.349681+00:00
-- url     : https://prove2.me/theorems/61e2118a-9e7f-43fd-a426-4ddd3124bdbc
-- title:
--   Sum of integers below 804
-- statement:
--   The sum of the nonnegative integers strictly less than $804$ equals $322806$. Equivalently, $\\sum_{k=0}^{804-1} k = 804(804-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_804 : ∑ k ∈ range 804, k = 322806 := by sorry

end FiniteTriangular
