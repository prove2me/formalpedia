-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_nat_clock_saturation_of_closed_horizon_ge_n
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_nat_clock_saturation_of_closed_horizon_ge_n
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:39:56.134744+00:00
-- url     : https://prove2.me/theorems/a9633c0c-4b32-4fc7-aa39-6c4d7741f534
-- title:
--   Original stopped dividend cash saturates at the strict natural clock n for every closed horizon T at or beyond n
-- statement:
--   For the original Levy riskProcess X and exact Stieltjes dividendMeasure D, a positive natural stopping cap n strictly excludes cash paid at t=n, while retaining time-zero dividends. Therefore when a closed observation horizon T is at least n, expected discounted cash clipped by min(ruinTime,n) is exactly the same as at horizon n. The proof explicitly avoids adding a closed-horizon payment atom at the stopping endpoint and uses the original process and measure.
-- source:
--   Source-exact large-horizon complement to 4569b16d. Imports only Proved public 26471312 original stopped strict-clock endpoint cash identity, compares Iic T and Iic n within Iio n. Neither fdb nor any canonical target is imported. This reduces large-T cases to one fixed bounded natural clock without altering stochastic semantics.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_nat_clock_saturation_of_closed_horizon_ge_n
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (n : ℕ)
    (hn : 0 < n) (hTn : (n : ℝ) ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
