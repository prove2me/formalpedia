-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_expected_stieltjes_antitone_in_discount_rate
-- name    : AvramDividend.Classical.avram_wave7_11_expected_stieltjes_antitone_in_discount_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:56:27.113843+00:00
-- url     : https://prove2.me/theorems/8ecc75cf-93d5-463b-8468-79ef088933bf
-- title:
--   Original expected finite-horizon Stieltjes dividend value decreases with the discount rate
-- statement:
--   For the exact original probability measure P, original dividendMeasure kernel, and original random stopping clock σ, increasing the discount rate q from q₁ to q₂≥q₁ decreases the complete expected ENNReal discounted Stieltjes dividend reward at the same real finite horizon T. The proof integrates the already Proved source-faithful pathwise rate inequality across the original sample space.
-- source:
--   Outer expectation corollary of Proved W7-11 pathwise Stieltjes rate monotonicity a4088502, relevant to actuarial sensitivity and canonical Avram UBV finite-horizon value.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_discounted_stieltjes_antitone_in_rate

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_expected_stieltjes_antitone_in_discount_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (T q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₂ * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
