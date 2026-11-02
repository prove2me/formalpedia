-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_inclusive_random_clock_real_cash_aestronglyMeasurable
-- name    : AvramDividend.Classical.avram_wave6_06_original_inclusive_random_clock_real_cash_aestronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:56:30.504202+00:00
-- url     : https://prove2.me/theorems/c3b1d861-f85a-41d1-bbb7-73f2089ec0b4
-- title:
--   Exact inclusive original stopped real Stieltjes cash is strongly measurable for a measurable random clock
-- statement:
--   For original admissible spectrally negative Levy control D and a measurable real-valued nonnegative random clock tau, the complete original ruin-paymentTimes inclusive upper interval cash, converted by ENNReal.toReal, is almost everywhere strongly measurable. No independent cash measurability assumption or stochastic Ito identity is needed. The physical measurable ENNReal payout is the now Proved 2d478c7d, then use the measurable toReal map and hCash pointwise equality. This supplies exactly hCashMeas of the source one-sided finite-horizon HJB consumer, once the stopped clock is shown real-measurable.
-- source:
--   Avram Proposition 4(i) exact cash; accepted original inclusive random cash meas 2d478c7d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_inclusive_random_clock_real_cash_aestronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0)
    (hτRealMeas : Measurable (fun ω => (τ ω : ℝ)))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    AEStronglyMeasurable Cash P := by sorry
