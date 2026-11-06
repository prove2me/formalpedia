-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_horizon_cash_eq_natural_ruin_stop
-- name    : AvramDividend.Classical.avram_limit2_original_strict_horizon_cash_eq_natural_ruin_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:14:09.286204+00:00
-- url     : https://prove2.me/theorems/f083a162-845e-4cf0-9bc8-210389854853
-- title:
--   Original ruin-stopped expected discounted dividend cash equals its strict positive real-horizon Stieltjes section
-- statement:
--   At strictly positive real horizon T, genuine original-process expected discounted dividendMeasure over min(ruinTime, ofReal T) equals genuine expected cash over paymentTimes(ruinTime) intersection Iio T. The public Proved paymentTimes identity 3634eef8 applies fibrewise; preserves time-zero atom while excluding any right-endpoint atom at T, with no vanishing terminal assumption, stochastic law replacement or measure equivalence.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_strict_horizon_cash_eq_natural_ruin_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by sorry
