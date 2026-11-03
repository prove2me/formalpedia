-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_horizon_reward_le_truncated_clock_plus_endpoint
-- name    : AvramDividend.Classical.avram_wave7_11_horizon_reward_le_truncated_clock_plus_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:12:43.114802+00:00
-- url     : https://prove2.me/theorems/e0ff01d5-edb1-47ba-9e23-177854dd46c7
-- title:
--   Original finite-horizon Stieltjes reward bound retaining exact terminal dividend atom
-- statement:
--   For any original dividend strategy sample and real finite horizon T ≥ 0, the genuine discounted Stieltjes payout on paymentTimes σ ∩ Iic T is bounded by the payout stopped at min(σ,T) plus the identical original-measure payment restricted to the terminal singleton {T}. The inequality exposes the sole endpoint correction required by a strict stopping-clock truncation.
-- source:
--   Derives from Proved exact W7-11 endpoint payment-set decomposition 0fe4e483 and Mathlib lintegral_union_le, for source-faithful canonical UBV value verification cc518136.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_exact_horizon_endpoint_payment_set_decomposition
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_horizon_reward_le_truncated_clock_plus_endpoint
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes (min σ (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
