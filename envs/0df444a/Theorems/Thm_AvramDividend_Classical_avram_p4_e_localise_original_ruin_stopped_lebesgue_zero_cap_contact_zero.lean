-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_lebesgue_zero_cap_contact_zero
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_stopped_lebesgue_zero_cap_contact_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:12:44.474919+00:00
-- url     : https://prove2.me/theorems/ff85326b-c871-4413-ae1e-992296ca2b64
-- title:
--   Original stopped UBV zero and cap contact from zero mass at the initial physical time
-- statement:
--   The actual original UBV stopped reserve spends zero μ-physical time at 0 and finite cap before ruin under the explicit source restriction μ {0}=0. The accepted positive-time source occupation handles all later times; the null mass at time zero removes the only endpoint obstruction. The result is about the deterministic physical-time generator clock, never about singular dividend Stieltjes mass.
-- source:
--   Accepted original source fulltime contact 227f802b-0070-4b5d-82a9-d536dcbea9cc and hZeroMass: μ {0}=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_fulltime_boundary_weight_zero_of_ae_positive
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A UBV controlled reserve spends zero atomless physical-generator time at zero or finite cap before a ruin-dominated clock. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_stopped_lebesgue_zero_cap_contact_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D s ω ≤ c)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] (hZeroMass : μ {0} = 0)
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        if (t : ℝ≥0∞) < τ ω ∧
          (riskProcess X x D t ω = 0 ∨
           riskProcess X x D t ω = c)
        then weight t ω else 0 ∂μ) = 0 := by sorry
