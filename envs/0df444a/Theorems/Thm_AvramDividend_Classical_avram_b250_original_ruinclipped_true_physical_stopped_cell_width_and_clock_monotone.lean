-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
-- name    : AvramDividend.Classical.avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:34:26.600561+00:00
-- url     : https://prove2.me/theorems/de2b51bf-699d-4534-af66-f718938bcd78
-- title:
--   Original ruin-clipped genuine physical mesh monotone and each stopped cell width at most n/(m+1)
-- statement:
--   For any genuine bounded stopping clock sigma and actual original physical grid v_i=min(i n/(m+1),sigma), every adjacent clock increment is nonnegative and its real-time duration is bounded by the deterministic physical cell width Δ=n/(m+1), including the unique partially stopped last cell. These exact pathwise geometric bounds are needed to instantiate the original B249 discounted Stieltjes cash gap estimate and the mixed Gaussian/negative-jump predictable energy bounds, without replacing the original stop or using anything after ruin.
-- source:
--   Elementary min truncation monotonicity and 1-Lipschitz behaviour: min(a+Δ,sigma) ≤ min(a,sigma)+Δ for a,Δ≥0, plus (i+1)Δ=iΔ+Δ. Cast NNReal to real.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
    (n m : ℕ) (σ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) * Δ) σ
    ∀ i : ℕ, v i ≤ v (i + 1) ∧
      ((v (i + 1) : ℝ) - (v i : ℝ)) ≤ (Δ : ℝ) := by sorry
