-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a98_original_gaussian_true_crossing_positive_cell_budget
-- name    : AvramDividend.Classical.avram_ga_a98_original_gaussian_true_crossing_positive_cell_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:35:22.110547+00:00
-- url     : https://prove2.me/theorems/87e0c74d-2b01-47cf-864d-261fd0fc9887
-- title:
--   Actual original stopped Gaussian crossing-cell positive Taylor error has one terminal budget regardless of mesh cell count
-- statement:
--   On the actual original uniform Gaussian physical grid n/(m+1), a single nonnegative upper budget on the positive stopped spatial crossing-cell source error also bounds the total crossing-masked positive error sum because the true crossing index set has at most one member.
-- source:
--   Direct sound original b0d9951c positive-only stopping-crossing finite grid error reduction via ga_a95 and ga_a97.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a98_original_gaussian_true_crossing_positive_cell_budget (n m : ℕ) (ρ : ℝ≥0)
    (f : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ i : ℕ, i < m →
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ →
      ρ ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) →
        max (f i) 0 ≤ B) :
    (∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ∧
        ρ ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
          ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
      then max (f i) 0 else 0) ≤ B := by sorry
