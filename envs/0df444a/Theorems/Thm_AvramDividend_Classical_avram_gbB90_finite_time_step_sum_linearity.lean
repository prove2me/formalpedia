-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB90_finite_time_step_sum_linearity
-- name    : AvramDividend.Classical.avram_gbB90_finite_time_step_sum_linearity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:18:13.322462+00:00
-- url     : https://prove2.me/theorems/ce176f09-9ac2-4eaf-bcd1-e862c5c88237
-- title:
--   Finite bounded-grid indicator sums commute with positive-horizon Lebesgue integration
-- statement:
--   The time integral of a finite sum of bounded-support uniform cell indicators is the finite sum of their time integrals. This is ordinary finite linearity of the Lebesgue integral on a bounded interval.
-- source:
--   Outer time-integral child of expected finite step interchange B88.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB90_finite_time_step_sum_linearity
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (A : ℕ → ℝ) :
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then A r else 0) ∂volume) =
      (Finset.range N).sum (fun r =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then A r else 0 ∂volume) := by sorry
