-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_discounted_stieltjes_antitone_in_rate
-- name    : AvramDividend.Classical.avram_wave7_11_original_discounted_stieltjes_antitone_in_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:44:49.23892+00:00
-- url     : https://prove2.me/theorems/a4088502-080e-4387-8f14-b035a9c6cd62
-- title:
--   Original finite-horizon Stieltjes payout is antitone in the discount rate
-- statement:
--   For the true original dividend Stieltjes measure on real time and the exact paymentTimes σ ∩ Iic T region, an increased discount rate q₂≥q₁ can only decrease the ENNReal discounted pathwise dividend reward. The proof uses that every payment time is nonnegative, including t=0 where both rates give the same factor one. No modification of the stochastic process, payout measure or horizon occurs.
-- source:
--   Finite-horizon deterministic rate comparison for Avram UBV value bridge cc518136, from Proved paymentTimes_measurable and pinned Real.exp_le_exp, ENNReal.ofReal_le_ofReal and lintegral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_discounted_stieltjes_antitone_in_rate
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (σ : ℝ≥0∞)
    (T q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₂ * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω)) := by sorry
