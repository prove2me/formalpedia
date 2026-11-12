-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB89_expected_fixed_time_step_sum_linearity
-- name    : AvramDividend.Classical.avram_gbB89_expected_fixed_time_step_sum_linearity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:18:09.144792+00:00
-- url     : https://prove2.me/theorems/eb80696f-7d20-486b-9ecc-56132a054d61
-- title:
--   At each fixed time expectation commutes with finite step-indicator sum
-- statement:
--   For a fixed time, every cell indicator is constant as a function of the probability-space variable. Linearity of the Bochner integral over a finite sum therefore interchanges expectation with the grid-indicator sum, provided each coefficient is integrable.
-- source:
--   Inner expectation child of finite time-expectation interchange B88.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB89_expected_fixed_time_step_sum_linearity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : ℕ) (δ t : ℝ) (F : ℕ → Ω → ℝ)
    (hF : ∀ r, Integrable (F r) P) :
    (∫ ω, (Finset.range N).sum (fun r =>
      if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
      then F r ω else 0) ∂P) =
    (Finset.range N).sum (fun r =>
      if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
      then (∫ ω, F r ω ∂P) else 0) := by sorry
