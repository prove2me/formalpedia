-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a33_original_uniform_grid_large_tail_L1_tendsto
-- name    : AvramDividend.Classical.avram_ga_a33_original_uniform_grid_large_tail_L1_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:18:01.844213+00:00
-- url     : https://prove2.me/theorems/23ae2a23-1d13-471e-b3b0-f9eaa495e82d
-- title:
--   Original Gaussian large-increment energy on the full uniform grid vanishes in expectation
-- statement:
--   For the original zero-jump Gaussian source over a physical uniform time mesh, the expected sum of normalized quadratic increments whose absolute size exceeds any fixed positive threshold converges to zero.
-- source:
--   Source-exact Gaussian A b0d9951c large-cell L1 estimate; compositions ga_a31 source fourth-grid tail and ga_a32 physical mesh rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a33_original_uniform_grid_large_tail_L1_tendsto
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
    (r : ℝ) (hr : 0 < r) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ
    Tendsto (fun m : ℕ =>
      ∫⁻ ω, ∑ i ∈ Finset.range m,
        ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
