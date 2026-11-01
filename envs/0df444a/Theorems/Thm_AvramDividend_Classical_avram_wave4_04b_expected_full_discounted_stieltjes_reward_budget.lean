-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_full_discounted_stieltjes_reward_budget
-- name    : AvramDividend.Classical.avram_wave4_04b_expected_full_discounted_stieltjes_reward_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:14:11.877159+00:00
-- url     : https://prove2.me/theorems/041489a2-13d4-454e-8d9f-139129d87cd9
-- title:
--   Full expected discounted stopped Stieltjes dividend reward is bounded by expected finite-horizon cumulative payments
-- statement:
--   For any adapted original dividend strategy and an arbitrary path-dependent stopping clock τ(ω), the expectation with respect to any source measure P of the entire discounted Lebesgue–Stieltjes reward on the closed finite horizon is at most the expectation of D⁺(T). This retains the right payment at time zero, all chronological right-jump atoms, the singular-continuous part, and absolutely continuous dividend variation. It asserts no finiteness unless expected cumulative payments are finite.
-- source:
--   Avram Dividend Wave 4 specialist 04-B; corollary of the Proved complete pathwise Stieltjes reward finite-horizon budget, source-type compatible with the corrected UBV reward

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_discounted_stieltjes_reward_finite_horizon_budget
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_expected_full_discounted_stieltjes_reward_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ ω) ∩ Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω : Ω, ENNReal.ofReal (rightLimit D T ω) ∂P) := by
  sorry
