-- Prove2me | Theorems.Thm_Erdos287_weighted_progression_error_le_variation
-- name    : Erdos287.weighted_progression_error_le_variation
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T21:55:53.557833+00:00
-- url     : https://prove2.me/theorems/80081acc-b2a8-4eaf-b5ef-ad23df1aac43
-- title:
--   Weighted progression discrepancy bounded by variation
-- statement:
--   Let q be positive and let f be a real sequence with f(N)=0. The absolute difference between the weighted sum over j<N in a fixed residue class modulo q and 1/q times the full weighted sum is at most the sum of |f(j+1)-f(j)| for j<N.
-- source:
--   Erdős #287, one-progression term of the regular Type II estimate.

import Mathlib

theorem Erdos287.weighted_progression_error_le_variation (q r N : ℕ) (hq : 0 < q) (f : ℕ → ℝ) (hzero : f N = 0) :
    |(∑ j ∈ Finset.range N, if Nat.ModEq q j r then f j else 0) -
        (∑ j ∈ Finset.range N, f j) / (q : ℝ)| ≤
      ∑ j ∈ Finset.range N, |f (j + 1) - f j| := by sorry
