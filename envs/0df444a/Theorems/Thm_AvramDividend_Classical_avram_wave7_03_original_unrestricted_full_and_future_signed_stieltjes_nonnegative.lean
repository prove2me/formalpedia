-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_full_and_future_signed_stieltjes_nonnegative
-- name    : AvramDividend.Classical.avram_wave7_03_original_unrestricted_full_and_future_signed_stieltjes_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:01:04.285179+00:00
-- url     : https://prove2.me/theorems/4743df8c-491e-4394-a448-5cb69a927316
-- title:
--   Full original unrestricted signed Stieltjes cash and all strict future payout tails are nonnegative
-- statement:
--   For every original dividend process path, the real signed Stieltjes discounted payout on the full exact source paymentTimes σ, and separately on every strict future window paymentTimes σ∩Ioi T, are nonnegative. The integrand exp(-q*t) is strictly positive for arbitrary real q, and the dividendMeasure is a nonnegative measure. This asserts only nonnegativity of the actual real integrals, and does not silently claim finiteness or IntegrableOn in the case of infinite ENNReal cash. The domain retains the time-zero right-limit atom for the full integral and continuous and jump payouts.
-- source:
--   Actual Definitions dividendMeasure and paymentTimes; Mathlib integral_nonneg and Real.exp_pos under exact domain measures.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_unrestricted_full_and_future_signed_stieltjes_nonnegative
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q : ℝ) :
    (0 ≤ ∫ t in paymentTimes σ,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∧
    (∀ T : ℝ, 0 ≤ ∫ t in paymentTimes σ ∩ Ioi T,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
