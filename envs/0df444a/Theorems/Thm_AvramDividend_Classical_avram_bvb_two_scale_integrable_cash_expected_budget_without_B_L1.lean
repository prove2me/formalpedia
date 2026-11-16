-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_two_scale_integrable_cash_expected_budget_without_B_L1
-- name    : AvramDividend.Classical.avram_bvb_two_scale_integrable_cash_expected_budget_without_B_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T11:25:06.343896+00:00
-- url     : https://prove2.me/theorems/c700a961-dd47-40ed-9b0f-8a03c5b60d5e
-- title:
--   Two-scale original BV cash bound yields expected reward ceiling without any integrability assumption on B
-- statement:
--   On a probability space, an integrable original stopped-cash reward F bounded by the initial candidate plus an integrable mean-zero martingale, a nonpositive possibly nonintegrable physical B, and two integrable positive error channels has expectation bounded by the candidate plus their error expectations. This is the precise B-elimination mechanism needed to deduce BV B verification without introducing an unnecessary B L1 premise.
-- source:
--   Drop the a.e nonpositive physical B directly in the pathwise inequality, then integrate the remaining integrable source and error terms. B integrability is never required.

import Mathlib
open MeasureTheory
open scoped Topology

theorem AvramDividend.Classical.avram_bvb_two_scale_integrable_cash_expected_budget_without_B_L1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (a : ℝ) (F M B E₁ E₂ : Ω → ℝ)
    (hF : Integrable F P)
    (hM : Integrable M P) (hM0 : (∫ ω, M ω ∂P) = 0)
    (hE₁ : Integrable (fun ω => max (E₁ ω) 0) P)
    (hE₂ : Integrable (fun ω => max (E₂ ω) 0) P)
    (hB : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ a + M ω + B ω + max (E₁ ω) 0 + max (E₂ ω) 0) :
    (∫ ω, F ω ∂P) ≤ a +
      (∫ ω, max (E₁ ω) 0 ∂P) +
      (∫ ω, max (E₂ ω) 0 ∂P) := by sorry
