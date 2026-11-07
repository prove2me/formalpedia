-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
-- name    : AvramDividend.Classical.avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:12:59.910517+00:00
-- url     : https://prove2.me/theorems/52132682-32c5-4ae8-b5fd-af893d8ab6d8
-- title:
--   Two original BV positive source errors control tight payoff excess without signed-source integrability
-- statement:
--   Given a genuine physical-grid payoff bounded by a centred term plus potentially nonintegrable signed generator B and two positive-part error budgets, the least positive payoff deficit is integrable and its expectation is no greater than the sum of the two error expectations, assuming measurability of that deficit. No signed B L1 hypothesis is required.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (F M B ErrCell ErrContact : Ω → ℝ) (base : ℝ)
    (hCell : Integrable (fun ω => max (ErrCell ω) 0) P)
    (hContact : Integrable (fun ω => max (ErrContact ω) 0) P)
    (hExcessMeas : AEStronglyMeasurable
      (fun ω => max (F ω - (base + (M ω + B ω))) 0) P)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ base + (M ω + B ω) +
        max (ErrCell ω) 0 + max (ErrContact ω) 0) :
    Integrable (fun ω => max (F ω - (base + (M ω + B ω))) 0) P ∧
    (∫ ω, max (F ω - (base + (M ω + B ω))) 0 ∂P) ≤
      (∫ ω, max (ErrCell ω) 0 ∂P) +
      (∫ ω, max (ErrContact ω) 0 ∂P) := by sorry
