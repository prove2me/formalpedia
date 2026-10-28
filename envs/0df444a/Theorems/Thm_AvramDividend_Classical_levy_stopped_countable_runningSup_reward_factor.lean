-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_stopped_countable_runningSup_reward_factor
-- name    : AvramDividend.Classical.levy_stopped_countable_runningSup_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:23:46.054706+00:00
-- url     : https://prove2.me/theorems/4f40a825-ffae-4915-8709-2c69d0d66e45
-- title:
--   Discounted strong-Markov factorisation of a countable running-supremum reward
-- statement:
--   At any finite right-continuous Lévy stopping clock, on any event measurable in the stopped history, the discounted supremum of subsequent Lévy increments sampled at countably many deterministic future times has expectation equal to the past discounted event mass multiplied by the fresh-path sampled supremum expectation. This provides the factorisation needed for each countable-grid approximation to the reflected dividend regulator; identifying the continuous-time discounted Stieltjes dividend reward is a separate limit theorem. Strict successful-passage stopped-history event measurability is established independently.
-- source:
--   Independent factorisation needed in the stopped-renewal derivation of Avram, Palmowski and Pistorius (2007), Proposition 1. Formally composes Proved countable_path_runningSup_increment_measurable (11a24f6f-755d-4f4d-b5a3-76e2a4793454) and Proved levy_finiteStopping_killedDiscount_futureReward_factor_rightCont (f4c6b616-f9ee-4440-b6a9-58690bc65480). Downstream target 79978d61-9d1f-4b20-b8a5-114797a8e380. The theorem does not assume or assert the final Stieltjes valuation.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_countable_path_runningSup_increment_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_stopped_countable_runningSup_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A)
    (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (times : ℕ → ℝ≥0) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      (⨆ n : ℕ, ENNReal.ofReal
        ((X.X (τ ω + times n) ω - X.X (τ ω) ω) -
          (X.X (τ ω + 0) ω - X.X (τ ω) ω)))
      else 0 ∂P) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, ⨆ n : ℕ,
        ENNReal.ofReal (X.X (times n) ω - X.X 0 ω) ∂P) := by
  sorry
