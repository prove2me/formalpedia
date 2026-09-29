-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_620
-- name    : FiniteTriangular.sum_range_620
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:48:06.266973+00:00
-- url     : https://prove2.me/theorems/c266c487-8cdc-41e5-bd34-4cedf91167a8
-- title:
--   Sum of integers below 620
-- statement:
--   The sum of the nonnegative integers strictly less than $620$ equals $191890$. Equivalently, $\\sum_{k=0}^{620-1} k = 620(620-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_620 : ∑ k ∈ range 620, k = 191890 := by sorry

end FiniteTriangular
