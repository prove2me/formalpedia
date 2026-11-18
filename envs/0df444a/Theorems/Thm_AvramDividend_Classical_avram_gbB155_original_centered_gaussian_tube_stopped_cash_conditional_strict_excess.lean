-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
-- name    : AvramDividend.Classical.avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:41:03.545951+00:00
-- url     : https://prove2.me/theorems/5b9adfdc-3319-4232-b0a4-1fa4b21dd56f
-- title:
--   Direct genuine original discounted Stieltjes cash and centered Gaussian tube noise imply strict fixed-band counterexample
-- statement:
--   On the original equal-cap reflected Gaussian path X=2t+B with Brownian tube |B|≤1/4000 and actual source tube |X|≤1/400 through T=1/1000, if the genuine strictly pre-ruin dividendMeasure cash integral is finite and the original physical source noise satisfies |N|≤1/4000, then the original discounted quadratic terminal payoff plus actual strict Stieltjes cash exceeds w(1/8)+N+1/1936. This direct counterexample avoids assuming any discounted stopped Itô cash identity; event positivity and source noise bound must still be established under the original process law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_short_barrier_terminal_reserve_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_gbB149_original_gaussian_barrier_dividends_quantitative_drift_lower
import Theorems.Thm_AvramDividend_Classical_avram_gbB150_original_gaussian_centered_tube_terminal_reserve_near_cap
import Theorems.Thm_AvramDividend_Classical_avram_gbB151_short_gaussian_cash_lower_and_noise_tube_strict_fixedband_excess
import Theorems.Thm_AvramDividend_Classical_avram_gbB154_original_gaussian_tube_strict_cash_real_lower_by_dividend_regulator
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSource : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ))
    (hTube : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |X.X s ω| ≤ (1 / 400 : ℝ))
    (hFinite : (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) ≠ ⊤)
    (N : ℝ) (hN : |N| ≤ (1 / 4000 : ℝ)) :
    ¬ (Real.exp (-(1 / 100000 : ℝ)) *
         (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
       (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal) -
         (3 / 16 : ℝ) ≤ N + (1 / 1936 : ℝ) := by sorry
