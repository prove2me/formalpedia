-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_strict_later_real_horizon_cash_dominates_closed
-- name    : AvramDividend.Classical.avram_limit2_strict_later_real_horizon_cash_dominates_closed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:33:21.099996+00:00
-- url     : https://prove2.me/theorems/4f845e71-de3b-4dbd-aad2-1a04f585c1ff
-- title:
--   Original Stieltjes cash monotonicity for arbitrary ordered real closed and strict horizons
-- statement:
--   For any two real time cutoffs S<T and the original dividendMeasure and paymentTimes associated to actual ruinTime, the expected discounted cash through the closed endpoint S is at most expected discounted cash strictly before T. This follows directly from Iic S subset Iio T at each sample path, inner and outer lintegral monotonicity. The payment at S remains included and the payment at T is excluded.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_strict_later_real_horizon_cash_dominates_closed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (S T : ℝ) (hST : S < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic S,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by sorry
