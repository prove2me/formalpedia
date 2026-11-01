-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_discounted_stieltjes_reward_finite_horizon_budget
-- name    : AvramDividend.Classical.avram_wave4_04b_complete_discounted_stieltjes_reward_finite_horizon_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:07:21.133164+00:00
-- url     : https://prove2.me/theorems/b8e7f7f7-d2a5-48e3-84ec-794dcdb1047a
-- title:
--   The complete discounted stopped Stieltjes dividend reward is bounded by paid finite-horizon total variation
-- statement:
--   For an arbitrary actual dividend strategy, q≥0, finite T and any stopped payment-time interval, the full positive discounted Lebesgue–Stieltjes payment integral over the closed finite horizon is no larger than the total right-continuous cumulative dividends D⁺(T). This includes the payment at time zero, all right jumps, absolutely continuous payments, and singular continuous payments.
-- source:
--   Avram Dividend Wave 4 specialist 04-B; full dividend measure on [0,T], positivity of discount

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_complete_discounted_stieltjes_reward_finite_horizon_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) ≤
      ENNReal.ofReal (rightLimit D T ω) := by
  sorry
