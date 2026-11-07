-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f12_masked_mean_budget_iff_positive_clock_excess_nonpositive
-- name    : AvramDividend.Classical.avram_p4_f12_masked_mean_budget_iff_positive_clock_excess_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:18:31.524996+00:00
-- url     : https://prove2.me/theorems/da68e4e6-f5f9-4cb9-87c9-51c60211883a
-- title:
--   Masked stopped expectation budget iff strictly positive clock source excess is nonpositive
-- statement:
--   On the original probability space, the stopped masked payoff has expectation at most its starting value b if and only if the signed excess of the unmasked payoff over b, restricted to strictly positive clocks, has nonpositive integral. This is a two-way reduction isolating the actual stochastic Ito-Meyer expectation obligation.
-- source:
--   P4-F12 exact zero-clock support identity; Bochner integrability and probability normalisation

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_p4_f12_masked_mean_budget_iff_positive_clock_excess_nonpositive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    [DecidablePred (fun ω : Ω => ω ∈ A)]
    (F : Ω → ℝ) (hF : Integrable F P) (b : ℝ) :
    (∫ ω, (if ω ∈ A then b else F ω) ∂P) ≤ b ↔
      (∫ ω in Aᶜ, F ω - b ∂P) ≤ 0 := by sorry
