-- Prove2me | Theorems.Thm_Erdos287_log_ratio_bound_with_unit_gaps
-- name    : Erdos287.log_ratio_bound_with_unit_gaps
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:20:29.667599+00:00
-- url     : https://prove2.me/theorems/ba34c505-6f2f-49da-8a9b-d31e5a121171
-- title:
--   A unit-gap correction to the logarithmic ratio bound
-- statement:
--   Let m and M be the extreme denominators of an Egyptian fraction representation of 1 with gaps at most two, and t the number of gaps of size one. Then log(M/m)+(t+2)/M≤2.
-- source:
--   Erdős Problem #287. Summation of the adjacent denominator ratio inequalities.

import Mathlib

theorem Erdos287.log_ratio_bound_with_unit_gaps (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2) :
    Real.log ((f (k - 1) : ℝ) / f 0) +
      ((((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card : ℝ) + 2) /
        f (k - 1) ≤ 2 := by sorry
