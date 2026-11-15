-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB233_martingale_FV_bounded_localtime_occupation_density
-- name    : AvramDividend.Classical.avram_gbB233_martingale_FV_bounded_localtime_occupation_density
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T10:26:24.846201+00:00
-- url     : https://prove2.me/theorems/90306061-dce6-4c35-bc8b-c5d24d3c65a3
-- title:
--   Gaussian martingale plus arbitrary finite-variation path has an almost surely finite bounded spatial occupation-time density
-- statement:
--   Under the exact martingale, square bracket, continuous path and pathwise locally bounded variation hypotheses of GB227, the actual original stopped physical reserve admits an almost-sure Lebesgue occupation-time density bounded by a finite random constant at all spatial levels, for every open interval. The density need only be Borel; continuous local time is not assumed, since finite-variation regulation can create spatial discontinuities. Requires a source stochastic-calculus occupation formula and pathwise local-time boundedness, which remain the genuine analytic task.
-- source:
--   Revuz-Yor/Protter occupation-time formula and local time for semimartingales; source-faithful GB227 Gaussian finite-variation random horizon.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB233_martingale_FV_bounded_localtime_occupation_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (Xsrc : ℝ≥0 → Ω → ℝ) (c σ : ℝ) (hσ : 0 < σ)
    (hM : Martingale (fun t ω =>
      Xsrc t ω - (t : ℝ) * c) 𝓕 P)
    (hQ : Martingale (fun t ω =>
      (Xsrc t ω - (t : ℝ) * c) ^ 2 -
      (t : ℝ) * σ ^ 2) 𝓕 P)
    (hContinuous : ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ≥0 => Xsrc t ω))
    (Dsrc : ℝ≥0 → Ω → ℝ)
    (hFV : ∀ ω, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => Dsrc t ω) Set.univ)
    (x : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ (ℓ : ℝ → ℝ≥0∞) (B : ℝ≥0∞),
      B ≠ ⊤ ∧
      (∀ z : ℝ, ℓ z ≤ B) ∧
      (∀ a b : ℝ,
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          x + Xsrc (Real.toNNReal t) ω -
            Dsrc (Real.toNNReal t) ω ∈ Set.Ioo a b} =
        ∫⁻ z in Set.Ioo a b, ℓ z ∂volume) := by sorry
