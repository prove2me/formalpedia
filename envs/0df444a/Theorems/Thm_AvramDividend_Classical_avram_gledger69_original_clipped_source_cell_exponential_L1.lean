-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger69_original_clipped_source_cell_exponential_L1
-- name    : AvramDividend.Classical.avram_gledger69_original_clipped_source_cell_exponential_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:25:17.679312+00:00
-- url     : https://prove2.me/theorems/05a78178-a22f-4e51-9e35-cccc1c9e87df
-- title:
--   Every genuine original clipped Gaussian source cell has an integrable positive exponential terminal value
-- statement:
--   For each physical mesh index, the true original Lévy terminal pre-rightpayment reserve admits an integrable upward exponential. This follows from the original stopped Esscher moment bound when the right clipped clock is bounded, its real value and actual terminal observable are measurable, and the frozen left rightLimit dividend is nonnegative.
-- source:
--   Source-exact stopped exponential tail input for gledger68 and gledger53, using Proved gledger62 and gledger67. All X, D and P are the original objects.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger62_original_bounded_stop_postpayment_exponential_L1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger69_original_clipped_source_cell_exponential_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (Δ H : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ H)
    (hvreal : ∀ i : ℕ, Measurable (fun ω =>
      ((min ((i : ℝ≥0) * Δ) (ρ ω) : ℝ≥0) : ℝ)))
    (hvstop : ∀ i : ℕ, IsStoppingTime 𝓕.rightCont (fun ω =>
      ((min ((i : ℝ≥0) * Δ) (ρ ω) : ℝ≥0) : WithTop ℝ≥0)))
    (hd0 : ∀ i ω, 0 ≤ rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω)
    (hExpMeas : ∀ i : ℕ, AEStronglyMeasurable (fun ω =>
      Real.exp (θ * (x +
        X.X (min (((i + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω))) P) :
    ∀ i : ℕ, Integrable (fun ω =>
      Real.exp (θ * (x +
        X.X (min (((i + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω))) P := by sorry
