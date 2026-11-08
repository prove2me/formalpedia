-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_negative_budget_L1_forced_by_positive_excess
-- name    : AvramDividend.Classical.avram_a19_negative_budget_L1_forced_by_positive_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:28:52.651202+00:00
-- url     : https://prove2.me/theorems/06c2f4b2-3d0d-4088-8ecc-164ae627fc85
-- title:
--   Positive-excess integrability forces L1 of a negative budget
-- statement:
--   For an everywhere nonpositive measurable budget B and integrable payoff/correction F,M, integrable positive excess over a+M+B forces integrability of B. Applied to A19, this exposes the hidden L1 requirement in a purported no-B-L1 estimate.
-- source:
--   Mathematical obstruction to original uniform BV generator integrability in Avram Classical.

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a19_negative_budget_L1_forced_by_positive_excess
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F M B : Ω → ℝ) (a : ℝ)
    (hF : Integrable F P) (hM : Integrable M P)
    (hBmeas : AEStronglyMeasurable B P)
    (hBnonpos : ∀ ω, B ω ≤ 0)
    (hExcess : Integrable
      (fun ω => max (F ω - (a + (M ω + B ω))) 0) P) :
    Integrable B P := by sorry
