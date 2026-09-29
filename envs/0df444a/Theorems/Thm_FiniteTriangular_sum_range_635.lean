-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_635
-- name    : FiniteTriangular.sum_range_635
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:51:37.863982+00:00
-- url     : https://prove2.me/theorems/69ba59a2-414f-4a4e-91bb-c3cbd8cefc17
-- title:
--   Sum of integers below 635
-- statement:
--   The sum of the nonnegative integers strictly less than $635$ equals $201295$. Equivalently, $\\sum_{k=0}^{635-1} k = 635(635-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_635 : ∑ k ∈ range 635, k = 201295 := by sorry

end FiniteTriangular
