-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finitecap_grid_discounted_kink_localtime_sum_nonpos
-- name    : AvramDividend.Classical.avram_jump6_B_original_finitecap_grid_discounted_kink_localtime_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:33:09.146394+00:00
-- url     : https://prove2.me/theorems/f4d48799-1b36-4c83-8f9d-93de4c63d697
-- title:
--   Original finite-cap discounted physical-grid kink local-time corrections have nonpositive sum
-- statement:
--   For a finite dividend cap and the original candidate w with derivative at least one strictly below the cap, each rational interior-cutoff Tanaka kink local-time correction is nonpositive at every grid cell. Any finite sum with nonnegative discounted weights and nonnegative local-time values is therefore nonpositive. This uses the Proved source finite-cap derivative kink sign and isolates the remaining stochastic local-time existence/integrability estimate without assuming finite negative-jump activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB47_original_finitecap_discounted_kink_localtime_correction_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_finitecap_grid_discounted_kink_localtime_sum_nonpos
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (S : Finset ℕ) (j : ℕ → ℕ)
    (L E : ℕ → ℝ)
    (hL : ∀ i ∈ S, 0 ≤ L i)
    (hE : ∀ i ∈ S, 0 ≤ E i) :    let b : ℕ → ℝ := fun i =>
      C.toReal * ((((j i + 1 : ℕ) : ℝ) / ((j i + 2 : ℕ) : ℝ)))
    (∑ i ∈ S, E i * (((1 - deriv w (b i)) / 2) * L i)) ≤ 0 := by sorry
