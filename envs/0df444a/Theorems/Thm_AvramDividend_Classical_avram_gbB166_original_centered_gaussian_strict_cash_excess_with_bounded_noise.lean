-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB166_original_centered_gaussian_strict_cash_excess_with_bounded_noise
-- name    : AvramDividend.Classical.avram_gbB166_original_centered_gaussian_strict_cash_excess_with_bounded_noise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:58:33.488274+00:00
-- url     : https://prove2.me/theorems/20e3a1ff-d9c5-4f60-a1fe-c928ad6a8669
-- title:
--   Original centered Gaussian tube and bounded physical noise strictly violate the fixed-band cash bound
-- statement:
--   For the original positive-drift Gaussian Lévy source represented as X_s=B_s+2s through T=1/1000, if the centred Brownian path stays within radius 1/4000 and the original stopped source noise N has magnitude at most 1/4000, the original genuine discounted strict Stieltjes cash and terminal reward strictly exceed the questioned fixed-band cap-linear inequality. The source tube, cash finiteness and strict excess follow from Proved B156, B163 and B155 via B165; the theorem does not assume the invalid cash upper bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB165_original_centered_gaussian_tube_strict_cash_excess_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB166_original_centered_gaussian_strict_cash_excess_with_bounded_noise
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
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal) -
         (3 / 16 : ℝ) ≤ N + (1 / 1936 : ℝ) := by sorry
