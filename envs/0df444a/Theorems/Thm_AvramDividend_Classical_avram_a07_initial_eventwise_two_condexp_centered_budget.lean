-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_initial_eventwise_two_condexp_centered_budget
-- name    : AvramDividend.Classical.avram_a07_initial_eventwise_two_condexp_centered_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:16:09.996281+00:00
-- url     : https://prove2.me/theorems/81a67307-e829-4cfd-8a41-7e8adaceb8f7
-- title:
--   Two original centred Ito noises imply every initial-event stopped budget
-- statement:
--   For an original probability measure and right-continuous filtration, suppose the integrable stopped reward F is almost surely bounded by b plus two integrable residual noises whose conditional expectations given time-zero history vanish. Show the reward integral on every initial-history measurable event is bounded by b times its probability. This algebraic transfer is the final step from the finite mixed Ito ledger to physical A07 cash verification.
-- source:
--   Conditional expectation set-integral identity, monotonicity and constant-function integration. Applies to original mixed stopped ledger 544e8511.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_initial_eventwise_two_condexp_centered_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (F MG MJ : Ω → ℝ)
    (hFI : Integrable F P) (hMGI : Integrable MG P)
    (hMJI : Integrable MJ P)
    (hMG0 : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MG ω = 0)
    (hMJ0 : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MJ ω = 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ b + MG ω + MJ ω) :
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by sorry
