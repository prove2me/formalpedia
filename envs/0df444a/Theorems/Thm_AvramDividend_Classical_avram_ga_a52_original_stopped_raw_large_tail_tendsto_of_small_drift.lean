-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a52_original_stopped_raw_large_tail_tendsto_of_small_drift
-- name    : AvramDividend.Classical.avram_ga_a52_original_stopped_raw_large_tail_tendsto_of_small_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:18:39.148087+00:00
-- url     : https://prove2.me/theorems/406299a3-3ece-4bc8-9848-c82d5ae4d584
-- title:
--   Original true-stop Gaussian raw physical large-increment squared energy vanishes in L1 under eventual small drift
-- statement:
--   The genuine original zero-jump Levy raw physical source increments, rather than only their drift-centred versions, have vanishing expected large-cell quadratic energy on the true pre-stop random mask, provided the deterministic mesh drift vanishes and the original centred sums are measurable.
-- source:
--   Original b0d9951c Gaussian compact postpayment positive Taylor raw spatial increment Lindeberg using source-exact a41 and a51.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a52_original_stopped_raw_large_tail_tendsto_of_small_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω => (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (η : ℝ) (hη : 0 < η)
    (hDrift : ∀ᶠ m in atTop, |(Δ m : ℝ) * X.c| ≤ η / 2)
    (hSumMeas : ∀ m : ℕ, Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal (if η / 2 ≤
            |X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
              X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c| then
            (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
              X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) ^ 2 else 0)
        else 0)) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
    Tendsto (fun m : ℕ => ∫⁻ ω, ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if η ≤
          |Z m i ω + (Δ m : ℝ) * X.c| then
          (Z m i ω + (Δ m : ℝ) * X.c) ^ 2 else 0)
      else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
