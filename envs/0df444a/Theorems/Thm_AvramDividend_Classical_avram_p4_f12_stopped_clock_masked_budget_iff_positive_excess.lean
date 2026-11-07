-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_clock_masked_budget_iff_positive_excess
-- name    : AvramDividend.Classical.avram_p4_f12_stopped_clock_masked_budget_iff_positive_excess
-- status  : Open
-- author  : @WillR
-- created : 2026-11-07T00:42:44.254903+00:00
-- url     : https://prove2.me/theorems/d0e86a61-c898-4007-8819-cd4de1b7fa05
-- title:
--   Stopped-clock masked budget equals strictly positive-clock signed excess
-- statement:
--   For a right-continuous-filtration nonnegative stopping clock and any integrable payoff on a probability space, the masked payoff budget is equivalent to nonpositivity of the signed payoff excess restricted to strictly positive clocks. This imports the independently proved stopping-time measurability and positive-clock residual formula, without stochastic source premises.
-- source:
--   Avram F12 published stopping-time zero event and measurable positive-clock integral budget

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f12_stopped_clock_masked_budget_iff_positive_excess
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ) (hF : Integrable F P) (b : ℝ) :
    (∫ ω, (if σ ω = 0 then b else F ω) ∂P) ≤ b ↔
      (∫ ω in {ω : Ω | σ ω ≠ 0}, F ω - b ∂P) ≤ 0 := by sorry
