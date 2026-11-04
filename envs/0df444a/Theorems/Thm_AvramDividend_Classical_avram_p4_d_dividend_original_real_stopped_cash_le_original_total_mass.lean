-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_stopped_cash_le_original_total_mass
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_real_stopped_cash_le_original_total_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:23:37.329711+00:00
-- url     : https://prove2.me/theorems/955ca106-2c80-4288-b1fa-26dc5a1fb332
-- title:
--   Genuine real stopped discounted dividend cash is positive and at most the entire original finite-horizon mass
-- statement:
--   If the real Cash term is defined by the source-exact ruin-stopped original discounted Stieltjes lintegral, then it is nonnegative and bounded above by the toReal value of the entire closed-horizon original dividend mass, represented by ENNReal.ofReal (rightLimit D T omega). This remains valid for all nonnegative discounts and all original dividend measures, including singular continuous and endpoint right atoms.
-- source:
--   Original source paymentTimes support and original bounded-kernel cash total-mass domination

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_bounded_kernel_cash_le_total_mass

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_real_stopped_cash_le_original_total_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (Cash : ℝ)
    (hCash : Cash =
      (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    0 ≤ Cash ∧
      Cash ≤ (ENNReal.ofReal (rightLimit D T ω)).toReal := by sorry
