-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a41_original_stopped_unnormalised_large_tail_tendsto
-- name    : AvramDividend.Classical.avram_ga_a41_original_stopped_unnormalised_large_tail_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:37:09.206313+00:00
-- url     : https://prove2.me/theorems/aaa0a1d8-dc5d-40ae-8b12-a94628c028cd
-- title:
--   Actual original stopped physical source Gaussian large increment quadratic energy vanishes in expectation
-- statement:
--   For the original zero-jump Levy process, arbitrary measurable random stop and physical uniform time mesh, expected quadratic energy from true unnormalised centred source Gaussian increments larger than any fixed positive threshold converges to zero.
-- source:
--   Exact original X/P/rightCont positive-only Taylor b0d9951c large-cell L1 input, derived from ga_a35 and ga_a40.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a41_original_stopped_unnormalised_large_tail_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω => (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ) (η : ℝ) (hη : 0 < η) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
    Tendsto (fun m : ℕ => ∫⁻ ω, ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if η ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0)
      else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
