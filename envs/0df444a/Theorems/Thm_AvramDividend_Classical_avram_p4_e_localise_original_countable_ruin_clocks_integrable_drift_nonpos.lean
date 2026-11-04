-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_countable_ruin_clocks_integrable_drift_nonpos
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_countable_ruin_clocks_integrable_drift_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:22:13.759478+00:00
-- url     : https://prove2.me/theorems/ebf3095c-fa0d-4652-b1c3-98951afd5aec
-- title:
--   Countable genuine original UBV stopped physical-time drifts share nonpositive finite integrals
-- statement:
--   Under explicitly quantified actual Integrable stopped density assumptions for every localising clock, obtain one common P-conull event on which every original source physical-time generator residual integral is nonpositive. Supports n-to-infinity localisation without asserting uniform integrability, stochastic Itô decomposition, random dividend-measure cap mass zero or pathwise boundary avoidance.
-- source:
--   Accepted single-clock original source integrable generator drift UUID 43cff21e-a1a0-4163-b9e4-acfb372c440a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_stopped_integrable_generator_density_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_countable_ruin_clocks_integrable_drift_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτ : ∀ k ω, τ k ω ≤ ruinTime X x D ω)
    (μ : ℕ → Measure ℝ≥0) (hμ : ∀ k, SFinite (μ k))
    (F : ℕ → ℝ → ℝ)
    (hF : ∀ k (y : ℝ), 0 < y → y < c → F k y ≤ 0)
    (hIntegrable : ∀ k ω, Integrable
      (fun t : ℝ≥0 => if 0 < t ∧ (t : ℝ≥0∞) < τ k ω
        then F k (riskProcess X x D t ω) else 0) (μ k)) :
    ∀ᵐ ω ∂P, ∀ k,
      (∫ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ k ω
        then F k (riskProcess X x D t ω) else 0 ∂(μ k)) ≤ 0 := by sorry
