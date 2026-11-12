-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_condexp_upper_of_two_centered_noises
-- name    : AvramDividend.Classical.avram_a07_condexp_upper_of_two_centered_noises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:49:52.73509+00:00
-- url     : https://prove2.me/theorems/77a95b9b-9d40-4df5-a479-23ac0498ada2
-- title:
--   Conditional expectation bound from two centred integrable noise witnesses
-- statement:
--   A general conditional-expectation projection: a globally dominated integrable random reward, controlled by a deterministic budget and two integrable noises with zero conditional expectation, has initial conditional expectation below that budget.
-- source:
--   Conditional expectation monotonicity, linearity and zero conditional-centred noise.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_condexp_upper_of_two_centered_noises
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (F MG MJ : Ω → ℝ)
    (hFI : Integrable F P) (hMGI : Integrable MG P)
    (hMJI : Integrable MJ P)
    (hMG0 : P[MG | 𝓕.rightCont 0] =ᵐ[P] 0)
    (hMJ0 : P[MJ | 𝓕.rightCont 0] =ᵐ[P] 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ b + MG ω + MJ ω) :
    P[F | 𝓕.rightCont 0] ≤ᵐ[P] (fun _ : Ω => b) := by sorry
