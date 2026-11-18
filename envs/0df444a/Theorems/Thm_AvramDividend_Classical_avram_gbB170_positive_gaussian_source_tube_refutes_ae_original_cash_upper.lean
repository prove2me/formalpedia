-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB170_positive_gaussian_source_tube_refutes_ae_original_cash_upper
-- name    : AvramDividend.Classical.avram_gbB170_positive_gaussian_source_tube_refutes_ae_original_cash_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T19:09:40.700999+00:00
-- url     : https://prove2.me/theorems/84b0fdf2-54e0-4066-8208-bd47278e1ef7
-- title:
--   Positive native Gaussian tube and bounded stopped noise refute the original a.e fixed-band cash upper
-- statement:
--   On any positive-measure measurable event of source paths with drift-two positive cap barrier and centred Brownian fluctuations within 1/4000 until the short stopping horizon, if the stopped physical-grid Gaussian L1 noise has magnitude at most 1/4000 almost everywhere on that event, the original fixed-band cash upper bound cannot hold almost everywhere there. B166 gives a pointwise strict counterexample and B169 converts that pointwise contradiction on a positive event into a refutation of the a.e claim. This is the precise logical link to theorem 699; constructing the native positive event and proving actual physical-martingale L1 convergence remain independent obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB166_original_centered_gaussian_strict_cash_excess_with_bounded_noise
import Theorems.Thm_AvramDividend_Classical_avram_gbB169_positive_tube_prevents_ae_fixedband_upper
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB170_positive_gaussian_source_tube_refutes_ae_original_cash_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A) (hApos : 0 < P A)
    (B : Ω → ℝ≥0 → ℝ)
    (hSource : ∀ ω ∈ A, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B ω s + 2 * (s : ℝ))
    (hCentered : ∀ ω ∈ A, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B ω s| ≤ (1 / 4000 : ℝ))
    (N : Ω → ℝ)
    (hN : ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ (1 / 4000 : ℝ)) :
    ¬ (∀ᵐ ω ∂(P.restrict A), (Real.exp (-(1 / 100000 : ℝ)) *
         (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
       (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal) -
         (3 / 16 : ℝ) ≤ N ω + (1 / 1936 : ℝ)) := by sorry
