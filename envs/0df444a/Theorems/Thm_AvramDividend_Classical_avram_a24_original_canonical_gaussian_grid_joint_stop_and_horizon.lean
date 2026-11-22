-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
-- name    : AvramDividend.Classical.avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:12:54.467359+00:00
-- url     : https://prove2.me/theorems/770898d3-8156-4cf2-806e-1c2b148498c6
-- title:
--   Original canonical stopped Gaussian grid has predictable start clocks and physical horizon bounds
-- statement:
--   For the actual canonical uniform Gaussian physical mesh, stopped at an arbitrary right-continuous stopping time bounded by the original deterministic horizon, every start clock is itself a right-continuous stopping time and is bounded by both the actual stopped clock and the horizon. This supplies the concrete stopping-time measurability and upper-horizon obligations of the original A24 Gaussian finite-cap source without modifying the underlying stochastic process.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_stopped_gaussian_uniform_time_grid_stopping
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (n : ℕ) (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let τg : ℕ → ℕ → Ω → ℝ≥0 := fun j i ω =>
      min ((i : ℝ≥0) * ((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) (σ ω)
    (∀ j i (t : ℝ≥0),
      MeasurableSet[𝓕.rightCont t] {ω : Ω | τg j i ω ≤ t}) ∧
    (∀ j i ω, τg j i ω ≤ (n : ℝ≥0)) ∧
    (∀ j i ω, τg j i ω ≤ σ ω):= by sorry
