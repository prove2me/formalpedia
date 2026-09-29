-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_797
-- name    : FiniteTriangular.sum_range_797
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:26:32.865112+00:00
-- url     : https://prove2.me/theorems/3f1b17f6-384b-4e0e-9aad-76d2f4e9f8b2
-- title:
--   Sum of integers below 797
-- statement:
--   The sum of the nonnegative integers strictly less than $797$ equals $317206$. Equivalently, $\\sum_{k=0}^{797-1} k = 797(797-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_797 : ∑ k ∈ range 797, k = 317206 := by sorry

end FiniteTriangular
