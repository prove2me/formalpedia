-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_393
-- name    : FiniteTriangular.sum_range_393
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:48:42.328997+00:00
-- url     : https://prove2.me/theorems/5646c581-e09c-4257-8bc3-1f1f17ae047d
-- title:
--   Sum of integers below 393
-- statement:
--   The sum of the nonnegative integers strictly less than $393$ equals $77028$. Equivalently, $\\sum_{k=0}^{393-1} k = 393(393-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_393 : ∑ k ∈ range 393, k = 77028 := by sorry

end FiniteTriangular
