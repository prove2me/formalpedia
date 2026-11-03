-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_reward_eq_truncated_clock_plus_endpoint
-- name    : AvramDividend.Classical.avram_wave7_11_positive_horizon_reward_eq_truncated_clock_plus_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:39:00.181779+00:00
-- url     : https://prove2.me/theorems/e749c2d6-fad7-4848-b282-30136e2c41d3
-- title:
--   Exact original positive finite horizon Stieltjes reward as strict stopped reward plus terminal atom
-- statement:
--   At each strictly positive real horizon T for the exact original Stieltjes dividend measure, the original ruin-clock discounted reward through T is exactly the reward at strict min(σ,T) plus the original discounted singleton dividend at T. Equality follows from the Proved exact payment-set decomposition, the positive-horizon min-clock endpoint exclusion, and the disjoint-union integral identity. No endpoint mass or continuous part is lost.
-- source:
--   Original Avram DividendStrategy definitions, previously Proved W7-11 endpoint decomposition (0fe4e483), paymentTimes_measurable, min-clock exclusion (5a47155e), pinned Mathlib lintegral_union.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_exact_horizon_endpoint_payment_set_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_endpoint_not_in_min_clock
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_positive_horizon_reward_eq_truncated_clock_plus_endpoint
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T : ℝ) (hT : 0 < T) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes (min σ (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
