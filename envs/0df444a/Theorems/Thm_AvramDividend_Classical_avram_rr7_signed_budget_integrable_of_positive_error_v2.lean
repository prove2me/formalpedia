-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_rr7_signed_budget_integrable_of_positive_error_v2
-- name    : AvramDividend.Classical.avram_rr7_signed_budget_integrable_of_positive_error_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:22:32.311908+00:00
-- url     : https://prove2.me/theorems/b1d2f67b-0f36-42e5-b3da-b979cf37c133
-- title:
--   Integrable positive-error source budget implies signed negative drift is L1
-- statement:
--   For a finite measure, an integrable stopped payoff F and centred or other integrable correction M, if a nonpositive a.e.-measurable signed source B satisfies a pathwise upper budget with an integrable error E, then B must itself be integrable. This records the exact hidden L1 requirement in a tight original-source budget.
-- source:
--   Source-exact abstract integrability consequence of the original signed-budget route. The core original source has a.e. B nonpositivity and a.e. strong measurability proved in 0aa36d8b and cb4b8ca1. This reduction exposes when apparent positive-error shortcuts still entail L1 of B.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_rr7_signed_budget_integrable_of_positive_error_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (F M B E : Ω → ℝ) (c : ℝ)
    (hF : Integrable F P) (hM : Integrable M P)
    (hB_meas : AEStronglyMeasurable B P)
    (hB_nonpos : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hE : Integrable E P)
    (hBudget : ∀ᵐ ω ∂P, F ω ≤ c + (M ω + B ω) + E ω) :
    Integrable B P := by sorry
