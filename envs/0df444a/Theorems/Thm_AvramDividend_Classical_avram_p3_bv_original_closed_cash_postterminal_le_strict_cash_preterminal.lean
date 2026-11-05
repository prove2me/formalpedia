-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_cash_postterminal_le_strict_cash_preterminal
-- name    : AvramDividend.Classical.avram_p3_bv_original_closed_cash_postterminal_le_strict_cash_preterminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:45:25.383336+00:00
-- url     : https://prove2.me/theorems/02b97e5d-b18a-44f4-bb9a-486de97d60fa
-- title:
--   At a positive original horizon, closed dividend cash plus postpayment terminal does not exceed strict cash plus prepayment terminal
-- statement:
--   An exact original-process horizon accounting inequality. The closed Stieltjes dividend integral is the strict pre-horizon cash plus the right-horizon atom only if the original controlled reserve survives. The stipulated actual right-payment secant bound pays the atom out of the difference between the pre- and post-rightpayment terminal value. On ruin at the horizon, the atom and both terminal branches vanish. No source process replacement, extra integrability or compensation is invoked.
-- source:
--   Proved original closed cash versus strict cash 54ad337e and the canonical right-jump secant hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The active closed-horizon right payment is paid out of the prepayment
terminal value, including the survival/ruin boundary distinction. -/

theorem AvramDividend.Classical.avram_p3_bv_original_closed_cash_postterminal_le_strict_cash_preterminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (S : ℝ≥0) (hS : 0 < S)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω)
       else 0) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
       else 0) := by sorry
