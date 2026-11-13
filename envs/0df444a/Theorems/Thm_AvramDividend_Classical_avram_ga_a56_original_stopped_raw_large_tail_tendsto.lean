-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a56_original_stopped_raw_large_tail_tendsto
-- name    : AvramDividend.Classical.avram_ga_a56_original_stopped_raw_large_tail_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T00:30:54.881197+00:00
-- url     : https://prove2.me/theorems/158120aa-aa84-4035-83dd-e39b00863337
-- title:
--   Actual original stopped Gaussian raw spatial large-increment squared energy vanishes in expected nonnegative integral
-- statement:
--   On the original zero-jump Lévy process and the true random stopping mask, the expected large raw-source squared increment energy of physical Gaussian cells tends to zero, assuming only original centred normalized increment measurability and genuine physical mesh width.
-- source:
--   Source-exact b0d9951c Gaussian positive interior compact C2 Taylor: ga_a52 raw stopped Lindeberg plus ga_a53 uniform drift and ga_a55 measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a56_original_stopped_raw_large_tail_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω => (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (η : ℝ) (hη : 0 < η) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
    Tendsto (fun m : ℕ => ∫⁻ ω, ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then
        ENNReal.ofReal (if η ≤
          |Z m i ω + (Δ m : ℝ) * X.c| then
          (Z m i ω + (Δ m : ℝ) * X.c) ^ 2 else 0)
      else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
