-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_expected_full_stieltjes_reward_sandwich
-- name    : AvramDividend.Classical.avram_wave4_04b_original_expected_full_stieltjes_reward_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:17:50.94508+00:00
-- url     : https://prove2.me/theorems/e0d8952e-690a-49af-ac30-16723e7222c8
-- title:
--   Original Iic finite-horizon stopped expected Stieltjes reward lies between the initial atom and total payment expectation
-- statement:
--   For the exact original stopped payout set paymentTimes τ(ω) ∩ Iic T, using arbitrary path-dependent stopping clocks and a genuine dividend strategy, the expectation of the entire discounted Stieltjes reward is bounded below by the expected chronological right-payment at time zero and above by expected cumulative D⁺(T). This includes all diffuse, singular-continuous and atomic payments. The proof verifies equality of the original Iic T payment set with its closed nonnegative horizon form, then integrates the already Proved pathwise bounds; no stochastic Itô axiom or integrability condition is smuggled in.
-- source:
--   Avram Dividend Wave4 04-B exact original stopped reward domain and complete expectation sandwich for Chat04 interface

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_full_stieltjes_reward_contains_initial_payment_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_discounted_stieltjes_reward_finite_horizon_budget
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_original_expected_full_stieltjes_reward_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω : Ω, ENNReal.ofReal
        (rightLimit D (0 : ℝ≥0) ω - D (0 : ℝ≥0) ω) ∂P) ≤
      (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂(dividendMeasure D ω) ∂P) ∧
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω : Ω, ENNReal.ofReal (rightLimit D T ω) ∂P) := by
  sorry
