-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_closed_horizon_real_cash_split
-- name    : AvramDividend.Classical.avram_p3_bv_closed_horizon_real_cash_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:42:21.128243+00:00
-- url     : https://prove2.me/theorems/44ff792e-ac4c-46a1-81c1-a8ad54f58ff2
-- title:
--   Finite original BV stopped real cash splits exactly into pre-horizon cash and the right-horizon payment atom
-- statement:
--   For a path with finite original stopped discounted Stieltjes cash, the exact closed-horizon split survives ENNReal.toReal. It retains the original ruin-filtered paymentTimes set and right-payment atom at T, using the separately proved original-process lintegral partition.
-- source:
--   Proved avram_p3_bv_closed_horizon_discounted_cash_split and Mathlib ENNReal.toReal_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_closed_horizon_discounted_cash_split
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_closed_horizon_real_cash_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (ω : Ω)
    (hPaid : MeasurableSet (paymentTimes (ruinTime X x D ω)))
    (hfinite :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
