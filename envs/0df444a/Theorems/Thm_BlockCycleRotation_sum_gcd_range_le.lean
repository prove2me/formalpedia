-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_gcd_range_le
-- name    : BlockCycleRotation.sum_gcd_range_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:12.618331+00:00
-- url     : https://prove2.me/theorems/c5c76b83-bb77-4696-92db-eec09ed57acc
-- title:
--   sum gcd range le
-- statement:
--   A supporting lemma of the formalization, declared as `sum_gcd_range_le`.
--
--   In Blomer–Bux this is **Thm 9**, “`∑_{k<n} gcd(n,k) = o(n²)`”. It is used in the proof of `theorem10_unit`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 9. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L929-L947

import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.sum_gcd_range_le {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Finset.range n, Nat.gcd n k ≤ n + 2 * (n * n.divisors.card) := by sorry
