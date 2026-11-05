-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:52:55.682941+00:00
-- url     : https://prove2.me/theorems/d58a7561-fe34-4843-a741-038cd01a33ee
-- title:
--   Literal original strict-horizon real dividend Cash equals initial right atom plus true open positive-time cash
-- statement:
--   For the exact original source process X and original admissible left-continuous/right-payment dividend control D, the literal real-valued once-discounted stopped Stieltjes payoff strictly before any positive finite horizon b equals its time-zero physical right dividend plus the original stopped (0,b) cash. The split preserves zero-time initial payout and all interior diffuse/singular/atomic payments, excludes the horizon atom and includes immediate ruin. Finiteness is sourced from the proved original closed dividend Cash theorem.
-- source:
--   Proved original paymentTimes inclusion/membership 71123237 and d68c1081; zero Stieltjes atom 1fb597ac and 0315346e; finite original cash c4e50d93; Mathlib lintegral_union, ENNReal.toReal_add.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_endpoint_exclusion_and_time_zero_payment
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (b : ℝ≥0) (hb : 0 < b) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    rightLimit D 0 ω +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
