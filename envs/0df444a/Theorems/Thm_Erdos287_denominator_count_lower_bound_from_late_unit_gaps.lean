-- Prove2me | Theorems.Thm_Erdos287_denominator_count_lower_bound_from_late_unit_gaps
-- name    : Erdos287.denominator_count_lower_bound_from_late_unit_gaps
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:28:09.510324+00:00
-- url     : https://prove2.me/theorems/0b0abf2d-b860-5112-8911-ef17b571bf73
-- title:
--   Late unit gaps increase the lower bound on the number of denominators
-- statement:
--   In an increasing unit-fraction representation of 1 with maximum denominator M and gaps at most two, if s selected unit gaps follow the first R denominators, then the number k of denominators satisfies 2k ≥ M(1−exp(−2−2Rs/M²)).
-- source:
--   Erdős Problem #287. Counting the remaining gaps gives a pointwise reciprocal comparison, including a penalty on the first R terms.

import Mathlib

theorem Erdos287.denominator_count_lower_bound_from_late_unit_gaps (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (R : ℕ) (hR : R ≤ k)
    (T : Finset ℕ) (hT : ∀ j ∈ T, j + 1 < k ∧ f (j + 1) - f j = 1)
    (hbefore : ∀ i < R, ∀ j ∈ T, i ≤ j) :
    let M := f (k - 1)
    (M : ℝ) - M * Real.exp (-2 - 2 * (R * ((T.card : ℝ) / (M : ℝ) ^ 2))) ≤ 2 * k := by sorry
