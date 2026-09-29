-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_695
-- name    : FiniteTriangular.sum_range_695
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:03:28.013118+00:00
-- url     : https://prove2.me/theorems/1d2b90b8-f730-4e70-9ca9-c3e3e7db65e5
-- title:
--   Sum of integers below 695
-- statement:
--   The sum of the nonnegative integers strictly less than $695$ equals $241165$. Equivalently, $\\sum_{k=0}^{695-1} k = 695(695-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_695 : ∑ k ∈ range 695, k = 241165 := by sorry

end FiniteTriangular
