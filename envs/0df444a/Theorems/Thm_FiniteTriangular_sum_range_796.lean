-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_796
-- name    : FiniteTriangular.sum_range_796
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:26:32.050965+00:00
-- url     : https://prove2.me/theorems/53a851dd-c880-4f04-87ac-6d864013bf66
-- title:
--   Sum of integers below 796
-- statement:
--   The sum of the nonnegative integers strictly less than $796$ equals $316410$. Equivalently, $\\sum_{k=0}^{796-1} k = 796(796-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_796 : ∑ k ∈ range 796, k = 316410 := by sorry

end FiniteTriangular
