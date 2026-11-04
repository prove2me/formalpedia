-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_bounded_kernel_cash_le_total_mass
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_bounded_kernel_cash_le_total_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:18:23.822031+00:00
-- url     : https://prove2.me/theorems/9280d010-7f8a-4dc8-8057-725f7bfdd4ff
-- title:
--   Any original ruin-stopped bounded payment kernel is dominated by full finite-horizon dividend Stieltjes mass
-- statement:
--   On an original dividend path, any extended ruin deadline and finite horizon, the literal integral of any ENNReal weight bounded by one over actual payment times is at most the full original closed-horizon dividend Stieltjes mass, exactly represented by finite rightLimit D T. Includes continuous/singular and both allowed endpoint atoms. This provides a reusable domination theorem for discounted and cutoff payment kernels.
-- source:
--   Source paymentTimes measurability/nonnegative support; original dividendMeasure total-mass rightLimit identity

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_bounded_kernel_cash_le_total_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (g : ℝ → ℝ≥0∞)
    (hg : ∀ u ∈ paymentTimes σ ∩ Iic (T : ℝ), g u ≤ 1) :
    (∫⁻ u in paymentTimes σ ∩ Iic (T : ℝ), g u ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D T ω) := by sorry
