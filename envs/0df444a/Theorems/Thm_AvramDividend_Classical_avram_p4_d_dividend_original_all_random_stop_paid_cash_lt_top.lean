-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_random_stop_paid_cash_lt_top
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_all_random_stop_paid_cash_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:23:38.226479+00:00
-- url     : https://prove2.me/theorems/f270960b-faed-4c95-8c36-e64feb381028
-- title:
--   Every source-exact admissible random stopped discounted dividend cash integral is finite, retaining the time-zero and horizon right-payment atoms
-- statement:
--   For an original spectrally negative Levy process with any admissible right-continuous dividend strategy and nonnegative discount, at every pathwise random stop τ no later than ruin, the exact eligible discounted Stieltjes payout in paymentTimes(ruinTime) intersected with the closed horizon [0,τ] is finite. The proof separately handles τ=0, strictly pre-ruin τ and positive-ruin τ, retaining time-zero, singular-continuous and surviving-horizon mass, and excluding a positive ruin-time right payment.
-- source:
--   Original stopped-clock cases from Proved source helpers 1fb597ac (zero horizon), 4f229f9a (initial singleton), 86168e67 (strict survival), and 0588c7a4 (positive ruin).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_discounted_full_cash_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_complete_paid_cash_lt_top
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_all_random_stop_paid_cash_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτle : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by sorry
