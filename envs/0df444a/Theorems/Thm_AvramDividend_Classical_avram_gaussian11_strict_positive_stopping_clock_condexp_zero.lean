-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussian11_strict_positive_stopping_clock_condexp_zero
-- name    : AvramDividend.Classical.avram_gaussian11_strict_positive_stopping_clock_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:13:48.321781+00:00
-- url     : https://prove2.me/theorems/eaa24ef3-604b-4057-9d9d-a9abfe199e39
-- title:
--   Conditional-centred integrals vanish on the strictly positive event of a stopped clock
-- statement:
--   For any probability measure and right-continuous filtration, a nonnegative stopping clock has a strictly positive event measurable at time zero. Therefore an integrable terminal variable with conditional expectation zero given the initial filtration also integrates to zero over that strictly positive clock event. Supports physical Gaussian stopped Itô martingale masking in Avram finite-cap conditional budgets.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_gaussian11_strict_positive_stopping_clock_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hCondZero : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) :
    (∫ ω in {ω : Ω | σ ω ≠ 0}, M ω ∂P) = 0 := by sorry
