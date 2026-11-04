-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_real_second_moment_tail_bound
-- name    : AvramDividend.Classical.avram_p2_j_ui_real_second_moment_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:48:37.166214+00:00
-- url     : https://prove2.me/theorems/eceef069-0285-4720-95a7-28822f863200
-- title:
--   Quantitative second-moment tail bound for measurable real random variables
-- statement:
--   For any real-valued measurable random variable Y on an arbitrary measure space and a finite positive threshold R, show that the ENNReal first-moment tail above R, multiplied by R, is bounded by the genuine squared e-norm integral of Y. This removes the abstract nonnegative envelope and its measurability proof, giving the exact real-variable uniform-integrability tail application from the independently Proved quantitative L2 tail theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_quantitative_l2_tail_lintegral

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_real_second_moment_tail_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (R : ℝ≥0) (hR : 0 < R) (K : ENNReal)
    (hK : (∫⁻ ω, ‖Y ω‖ₑ ^ (2 : ℕ) ∂P) ≤ K) :
    (R : ENNReal) * (∫⁻ ω,
      (if (R : ENNReal) ≤ ‖Y ω‖ₑ then ‖Y ω‖ₑ else 0) ∂P) ≤ K := by sorry
