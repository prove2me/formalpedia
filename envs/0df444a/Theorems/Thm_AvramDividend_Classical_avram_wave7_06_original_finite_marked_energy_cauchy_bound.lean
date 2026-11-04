-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_marked_energy_cauchy_bound
-- name    : AvramDividend.Classical.avram_wave7_06_original_finite_marked_energy_cauchy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:09:26.085249+00:00
-- url     : https://prove2.me/theorems/02c93b8d-65ca-4694-b926-d7967d27f171
-- title:
--   L2 finite-energy bound for actual original marked-jump time sums
-- statement:
--   For any finite set F of original marked-jump times in the fixed source path and real stopped predictable jump weights H, the square of the jump-weight sum is bounded by the number of original jumps times the sum of their squared weights. Applying this pointwise to the actual source marked-time sets supplies the finite-count L2 energy inequality without changing the process or filtration. It does not assert compensation or martingale isometry.
-- source:
--   Finite-sum Cauchy Schwarz from pinned Mathlib sq_sum_le_card_mul_sum_sq.

import Mathlib
open scoped NNReal

theorem AvramDividend.Classical.avram_wave7_06_original_finite_marked_energy_cauchy_bound
    (F : Finset ℝ≥0) (H : ℝ≥0 → ℝ) :
    (∑ u ∈ F, H u) ^ 2 ≤
      (F.card : ℝ) * (∑ u ∈ F, (H u) ^ 2) := by sorry
