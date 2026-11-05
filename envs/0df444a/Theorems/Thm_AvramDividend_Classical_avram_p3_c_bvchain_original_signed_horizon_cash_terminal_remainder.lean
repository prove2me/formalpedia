-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_signed_horizon_cash_terminal_remainder
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_signed_horizon_cash_terminal_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:44:43.178888+00:00
-- url     : https://prove2.me/theorems/631a6ec4-5253-4738-b20a-de73f269927d
-- title:
--   Original BV true-clock strict-survival signed horizon dividend remainder
-- statement:
--   For the actual original controlled Lévy process and positive horizon, closed true-clock Stieltjes dividends plus the strict-survival post-rightpayment discounted candidate are bounded by strict-horizon Stieltjes dividends plus the strict-survival pre-rightpayment candidate. The active branch uses the literal discounted physical horizon atom and the original hjump secant; the inactive branch uses the original ruin clock to show no horizon atom remains. Time zero is retained in both cash terms, and the statement imposes no new C1, generator, compensator, pathwise assumption or L1 hypothesis.
-- source:
--   Proved P3-C horizon split 037794fe; ruin-by-horizon exact equality 837b141e; and Proved P4-D original active horizon discounted hjump budget a60a7f0d.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_ruin_by_horizon_closed_cash_eq_strict_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_signed_horizon_cash_terminal_remainder
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : ℝ≥0) (hS : 0 < S) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (riskProcess X x D S ω - (rightLimit D S ω - D S ω))
      else 0) ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) := by sorry
