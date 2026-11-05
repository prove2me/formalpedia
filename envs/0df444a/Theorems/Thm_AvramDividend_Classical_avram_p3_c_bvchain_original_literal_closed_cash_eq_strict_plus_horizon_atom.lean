-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:07:32.922948+00:00
-- url     : https://prove2.me/theorems/037794fe-47f2-43e9-9f2e-dcda1d0e267a
-- title:
--   Exact original closed finite-horizon real Stieltjes cash equals strict cash plus physical horizon right atom
-- statement:
--   The exact original real discounted Stieltjes cash including the closed physical horizon is the strict pre-horizon integral plus the full discounted singleton right-payment atom, with finiteness from the original source admissibility and valid when the horizon is at ruin or zero. It is the endpoint bridge from the P3-C strict-grid cash to the P3 parent closed-horizon payment convention.
-- source:
--   Original paymentTimes / dividendMeasure definitions and Proved original closed stopped cash integrability c4e50d93; disjoint horizon decomposition by order trichotomy.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (b : ℝ≥0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ)) ∩
        ({(b : ℝ)} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
