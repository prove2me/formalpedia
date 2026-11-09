-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_condexp_upper_to_centered_majorant
-- name    : AvramDividend.Classical.avram_mix_fin13_condexp_upper_to_centered_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:28:16.389202+00:00
-- url     : https://prove2.me/theorems/2601d430-bd1f-4522-b519-0fc905db5f08
-- title:
--   Conditional upper bound yields an integrable initially centred pointwise majorant
-- statement:
--   On a probability space with sub-sigma-algebra G, an integrable real reward whose conditional expectation given G is at most a constant b admits an integrable residual with zero conditional expectation and an almost-everywhere upper majorant by b plus the residual. Choose the reward minus its conditional expectation. This is the exact algebraic final step needed by the corrected finite-activity Avram mixed source theorem.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin13_condexp_upper_to_centered_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ)
    (hUpper : ∀ᵐ ω ∂P, condExp G P F ω ≤ b) :
    ∃ M : Ω → ℝ, Integrable M P ∧
      (∀ᵐ ω ∂P, condExp G P M ω = 0) ∧
      (∀ᵐ ω ∂P, F ω ≤ b + M ω) := by sorry
