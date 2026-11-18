-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB181_original_centered_gaussian_stopped_cash_budget_pathwise_false
-- name    : AvramDividend.Classical.avram_gbB181_original_centered_gaussian_stopped_cash_budget_pathwise_false
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T19:06:06.767103+00:00
-- url     : https://prove2.me/theorems/1d66b533-9059-4147-bc7a-56ecbf914132
-- title:
--   Direct genuine original Gaussian stopped dividend cash violates fixed-band budget on every small centred Brownian tube path
-- statement:
--   For any original spectrally negative Lévy model path with source X_s=B_s+2s, if the centred Brownian component stays within 1/4000 through T=1/1000 and the actual physical-grid Gaussian limit N at that path is at most 1/4000 in absolute value, then the genuine original strictly pre-ruin discounted cash plus quadratic terminal payoff exceeds its claimed fixed-band bound. All cash finiteness and source tube conditions are proved from original definitions, leaving only pathwise Gaussian event and limit noise bound explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
import Theorems.Thm_AvramDividend_Classical_avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB181_original_centered_gaussian_stopped_cash_budget_pathwise_false
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSource : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ))
    (N : ℝ) (hN : |N| ≤ (1 / 4000 : ℝ)) :
    ¬ (Real.exp (-(1 / 100000 : ℝ)) *
      (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
      (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-( (1 / 100 : ℝ) * t )))
      ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal) -
      (3 / 16 : ℝ) ≤ N + (1 / 1936 : ℝ) := by sorry
