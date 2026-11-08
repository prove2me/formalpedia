-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_law_predictable_clock_signed_fubini
-- name    : AvramDividend.Classical.avram_ubv_top9_original_law_predictable_clock_signed_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:51:23.119481+00:00
-- url     : https://prove2.me/theorems/983f01df-cc46-4dc0-9511-5d3caf99cc65
-- title:
--   Original probability-law predictable finite-clock signed Fubini equality
-- statement:
--   For the original source probability law and a finite physical horizon, an integrable predictable integrand can be integrated first in physical time and then in the probability law, and the resulting expectation equals the original predictable-clock integral. This is the signed Fubini equality with the exact source clock, not an extension to a new stochastic process or filtration.
-- source:
--   Mathlib exact pin integral_integral_swap, integral_prod, integrable_of_integrable_trim and integral_trim_ae; source X.isProbability and accepted predictable inclusion from 55a364af. Follows the proved fibre integrability specialisation 5986fea6 without changing the original source probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_law_predictable_clock_signed_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (R : ℝ≥0 × Ω → ℝ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμeq : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hR : Integrable R μ) :
    (∫ ω : Ω, ∫ t : ℝ≥0, R (t, ω) ∂
      (((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal) ∂P) =
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω, R p ∂μ) := by sorry
