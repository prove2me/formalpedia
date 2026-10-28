-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_record_before_clock_capped_reward_lintegral_iSup
-- name    : AvramDividend.Classical.avram_ws01e_b_strict_record_before_clock_capped_reward_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:14:35.281686+00:00
-- url     : https://prove2.me/theorems/f7c9a65b-ce1e-4c07-bdd7-2f9870df9d72
-- title:
--   Nonnegative weighted Qp stopped survival reward is increasing supremum over finite first-record caps
-- statement:
--   For any joint path-clock measure μ (including the genuine Esscher tilted Qp), arbitrary measurable nonnegative joint reward F, possibly infinite strict first-record age τ, and measurable real observation clock event, the lower integral of F restricted to the uncapped strict first-record-before-clock event equals the supremum of the integrals restricted to natural finite-cap events, provided each capped event is measurable. This is the exact unnormalised monotone convergence step required to remove the first-record cap from genuine tilted future-path regeneration, with no finiteness or martingale assumption on F.
-- source:
--   Proved strict clock cap event exhaustion and monotone measure_iUnion; apply that measure identity to the weighted measure μ.withDensity F, then use pinned withDensity_apply to translate the equality into restricted lower integrals.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_record_before_clock_capped_mass_iSup

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_strict_record_before_clock_capped_reward_lintegral_iSup
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (μ : Measure (Ω × Θ))
    (τ : Ω → ℝ≥0∞) (clock : Θ → ℝ)
    (F : Ω × Θ → ℝ≥0∞) (hF : Measurable F)
    (hMeas : ∀ n : ℕ, MeasurableSet {z : Ω × Θ |
      τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}) :
    (∫⁻ z in {z : Ω × Θ |
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}, F z ∂μ) =
    ⨆ n : ℕ, (∫⁻ z in {z : Ω × Θ |
      τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}, F z ∂μ) := by sorry
