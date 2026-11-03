-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_weak_future_clock_exact_horizon_endpoint_correction
-- name    : AvramDividend.Classical.avram_wave7_11_weak_future_clock_exact_horizon_endpoint_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:11:18.429673+00:00
-- url     : https://prove2.me/theorems/3dfaf6e8-cf57-4686-859a-d4eb01dabbaa
-- title:
--   Exact positive-horizon Stieltjes endpoint correction at weakly future auxiliary clock
-- statement:
--   For the canonical Stieltjes dividendMeasure D and paymentTimes stopping set, a non-strictly later auxiliary truncation clock η≥ENNReal.ofReal T changes the finite-horizon reward only when η equals the observation horizon. In that equality case, the missing amount is exactly the original discounted horizon singleton payout. This is an exact pathwise source-measure equality, with no assumption that the singleton has zero mass. For η>T, the correction is zero.
-- source:
--   Proved W7-11 positive-horizon exact endpoint decomposition e749c2d6-fad7-4848-b282-30136e2c41d3 and strict-future payment set equality e57ac9e9-1cd4-4321-8da3-408eb9bcc0e7.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_reward_eq_truncated_clock_plus_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_strict_future_clock_preserves_finite_payment_set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_weak_future_clock_exact_horizon_endpoint_correction
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ η : ℝ≥0∞) (q T : ℝ)
    (hT : 0 < T) (hFuture : ENNReal.ofReal T ≤ η) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes (min σ η) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (if η = ENNReal.ofReal T then
      (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      else 0) := by sorry
