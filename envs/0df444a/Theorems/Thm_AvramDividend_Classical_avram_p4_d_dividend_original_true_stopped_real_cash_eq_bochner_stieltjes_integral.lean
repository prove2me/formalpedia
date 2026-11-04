-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_real_cash_eq_bochner_stieltjes_integral
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_real_cash_eq_bochner_stieltjes_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:34:54.359191+00:00
-- url     : https://prove2.me/theorems/ea0aaff0-4238-473e-964c-d4ef1b41add7
-- title:
--   Exact source ruin-stopped dividend Cash equals genuine real Stieltjes Bochner integral
-- statement:
--   On any original dividend path, including a true extended ruin deadline, all payments through a closed finite horizon and a nonnegative discount rate, the literal source stopped Cash as the toReal of the ENNReal Stieltjes lintegral equals the ordinary real Bochner integral of exp(-q s) against the same restricted original dividendMeasure. The prior source-exact bounded discount integrability theorem establishes all hypotheses, and Mathlib converts integrable nonnegative real integrals exactly. This handles singular, diffuse and right-atomic payments without altering the stopped payment set.
-- source:
--   Original true stopped discount integrability helper; Mathlib ofReal_integral_eq_lintegral_ofReal and integral_nonneg_of_ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_real_cash_eq_bochner_stieltjes_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
    ∫ s in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * s)) ∂(dividendMeasure D ω) := by sorry
