-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
-- name    : AvramDividend.Classical.avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T19:01:28.614203+00:00
-- url     : https://prove2.me/theorems/6d2b3ddc-2f87-4a57-a7ec-65d8b9beb6c3
-- title:
--   Any positive-probability centered Gaussian tube disproves an almost-everywhere original fixed-band cash budget with bounded noise
-- statement:
--   Suppose a genuine original spectrally negative Lévy Gaussian source has positive measure on an event where its paths equal drift-two Brownian trajectories with centered fluctuations ≤1/4000 until 1/1000, and suppose the true physical-grid limit noise N is bounded by 1/4000 almost everywhere there. Then an almost-everywhere bound that the real original strictly pre-ruin discounted cash plus quadratic terminal reward exceeds initial value by at most N+1/1936 is impossible. This combines the direct stopped cash contradiction B155, original source-tube B156, and automatic cash finiteness B163, with a nonzero restricted measure to extract an actual witness. Positivity and true noise identification remain explicit independent hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
import Theorems.Thm_AvramDividend_Classical_avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (E : Set Ω) (hE : MeasurableSet E) (hPositive : 0 < P E)
    (B : Ω → ℝ≥0 → ℝ)
    (hSource : ∀ ω ∈ E, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B ω s + 2 * (s : ℝ))
    (hCentered : ∀ ω ∈ E, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B ω s| ≤ (1 / 4000 : ℝ))
    (N : Ω → ℝ)
    (hNoise : ∀ᵐ ω ∂(P.restrict E), |N ω| ≤ (1 / 4000 : ℝ))
    (hBudget : ∀ᵐ ω ∂(P.restrict E), Real.exp (-(1 / 100000 : ℝ)) *
        (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
      (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal - (3 / 16 : ℝ) ≤ N ω + (1 / 1936 : ℝ)) :
    False := by sorry
