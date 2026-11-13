-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_stopped_mask_uniform_tail_tendsto
-- name    : AvramDividend.Classical.avram_ga_a35_original_stopped_mask_uniform_tail_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:24:51.608918+00:00
-- url     : https://prove2.me/theorems/faa76173-7b94-466d-a768-512446dd0581
-- title:
--   Original random-stopped full-grid Gaussian large quadratic energy vanishes in expectation
-- statement:
--   On the original zero-jump Gaussian process, large Gaussian source quadratic increments summed only over uniform mesh cells strictly preceding any random stopping clock converge to zero in expected nonnegative integral.
-- source:
--   Direct positive-only stopped Taylor large-cell child for b0d9951c, conditional on physical original-grid large-tail vanishing proved by a33.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a35_original_stopped_mask_uniform_tail_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω =>
        (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
          X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ))
    (ρ : Ω → ℝ≥0) (r : ℝ) (hr : 0 < r) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ
    Tendsto (fun m : ℕ =>
      ∫⁻ ω, ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0)
        else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
