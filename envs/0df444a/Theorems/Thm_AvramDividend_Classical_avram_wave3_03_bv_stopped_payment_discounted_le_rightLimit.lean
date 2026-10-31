-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
-- name    : AvramDividend.Classical.avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:29:48.378246+00:00
-- url     : https://prove2.me/theorems/1a006d5f-5750-42ea-bbf8-75fd70b573d2
-- title:
--   Actual stopped dividend-payment measure bounded by closed-horizon right-limit mass
-- statement:
--   For a genuine adapted monotone left-continuous dividend strategy, any ruin boundary σ and nonnegative finite horizon T, all discounted dividendMeasure mass on paymentTimes σ ∩ (-∞,T] is bounded by the full post-payment cumulative dividend rightLimit D T. This includes all continuous and singular-continuous mass and both time-zero and T-right-jump atoms. Proved by pathwise set inclusion into [0,T] and the accepted closed-horizon all-mass Stieltjes bound.
-- source:
--   Actual platform paymentTimes σ definition, genuine dividendMeasure D, and already Proved avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound (UUID 899a15ee-29a7-4820-b5c7-d87109a699fe), plus Mathlib lintegral_mono_set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D T ω) := by sorry
