-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_long_joint_tube_original_zero_noise_cash_excess
-- name    : AvramDividend.Classical.avram_gaussianB_long_joint_tube_original_zero_noise_cash_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:41:08.670993+00:00
-- url     : https://prove2.me/theorems/0d4c798b-f7e9-49f9-8c06-d7580ef2312d
-- title:
--   Original Gaussian longer joint tube forces strict genuine stopped cash violation for zero martingale
-- statement:
--   For any original equal-cap reflected Lévy source with short drift-two Gaussian path and a joint centred and source supnorm tube through 17/16000, its actual strictly pre-ruin discounted dividendMeasure cash and quadratic terminal payoff exceed the fixed-band allowance with martingale term N=0. The genuine cash finiteness is proved automatically using B163, and B155 supplies the strict numerical excess. A separate argument is still needed to identify or bound the actual original stopped physical-grid martingale N.

import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
import Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_long_joint_tube_original_zero_noise_cash_excess
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSourceLong : ∀ s : ℝ≥0, s ≤ (17 / 16000 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCenteredLong : ∀ s : ℝ≥0, s ≤ (17 / 16000 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ))
    (hTubeLong : ∀ s : ℝ≥0, s ≤ (17 / 16000 : ℝ≥0) →
      |X.X s ω| ≤ (1 / 400 : ℝ)) :
    ¬ (Real.exp (-(1 / 100000 : ℝ)) *
         (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
       (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal) -
         (3 / 16 : ℝ) ≤ (1 / 1936 : ℝ) := by sorry
