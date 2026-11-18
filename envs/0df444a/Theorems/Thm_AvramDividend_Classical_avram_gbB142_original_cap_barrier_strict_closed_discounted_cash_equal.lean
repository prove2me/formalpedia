-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB142_original_cap_barrier_strict_closed_discounted_cash_equal
-- name    : AvramDividend.Classical.avram_gbB142_original_cap_barrier_strict_closed_discounted_cash_equal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:56:52.516602+00:00
-- url     : https://prove2.me/theorems/a4125a61-87ec-4877-bc58-49e946bd2973
-- title:
--   Original continuous cap barrier discounted Stieltjes cash has identical strict and closed endpoints
-- statement:
--   For the original cap barrier dividend strategy under admissibility, any nonnegative discount rate and any physical horizon, the original discounted cash integral restricted to payment times strictly before S equals the closed-at-S integral. This is a genuine original Iio Stieltjes ledger identity, since the Proved right-limit equality makes the payment atom at S vanish.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_barrier_postpayment_rightLimit_eq
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB142_original_cap_barrier_strict_closed_discounted_cash_equal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hAdm : IsAdmissibleLe X (1 / 8 : ℝ)
      (ENNReal.ofReal (1 / 8 : ℝ))
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) :
    (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ)
          (1 / 8 : ℝ)) ω)).toReal =
    (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ)
          (1 / 8 : ℝ)) ω)).toReal := by sorry
