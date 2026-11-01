-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_stieltjes_reward_localisation_supremum
-- name    : AvramDividend.Classical.avram_wave4_04b_complete_stieltjes_reward_localisation_supremum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:44:23.932887+00:00
-- url     : https://prove2.me/theorems/8f6071fe-9078-40b5-ab16-c8c4e4b277a0
-- title:
--   Full weighted dividend Stieltjes reward commutes with increasing interior stopping-clock localisation
-- statement:
--   For an actual filtered dividend strategy, a path, a finite horizon, arbitrary nonnegative measurable reward weight and monotone increasing extended stopping clocks, the complete Stieltjes reward up to the supremum clock is exactly the supremum of rewards up to the approximating clocks. The original chronological paymentTimes convention retains the initial right atom t=0, all other right payments, absolutely continuous dividend variation and singular-continuous dividend variation without atom-concentration assumptions. This is the monotone convergence/localisation ingredient for the later genuine Itô–Meyer balance, not an asserted stochastic martingale formula.
-- source:
--   04-B source dividendMeasure and paymentTimes; pinned Mathlib lintegral_iSup, measurable indicator and right-payment clock union

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_payment_times_supremum_clock_union

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_complete_stieltjes_reward_localisation_supremum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (τ : ℕ → ℝ≥0∞) (hτ : Monotone τ)
    (v : ℝ → ℝ≥0∞) (hv : Measurable v) :
    (∫⁻ s in paymentTimes (⨆ n, τ n) ∩ Iic (T : ℝ),
      v s ∂dividendMeasure D ω) =
    ⨆ n, (∫⁻ s in paymentTimes (τ n) ∩ Iic (T : ℝ),
      v s ∂dividendMeasure D ω) := by
  sorry
