-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_discard_nonL1_negative_generator_before_expectation
-- name    : AvramDividend.Classical.avram_bv_strict10_discard_nonL1_negative_generator_before_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:21:09.663746+00:00
-- url     : https://prove2.me/theorems/918345cc-9254-4bc3-b1b0-05ce7c8185d7
-- title:
--   Original nonnegative payoff budget drops nonintegrable negative BV generator before taking expectations
-- statement:
--   If a nonnegative original stopped dividend payoff is bounded pointwise by base plus a centred integrable martingale, a nonpositive signed generator, and two integrable positive errors, then the payoff is integrable and its expectation is bounded by base plus both error expectations. The signed generator is never integrated.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict10_discard_nonL1_negative_generator_before_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F M B ErrCell ErrContact : Ω → ℝ) (base : ℝ)
    (hM : Integrable M P) (hMzero : (∫ ω, M ω ∂P) = 0)
    (hCell : Integrable (fun ω => max (ErrCell ω) 0) P)
    (hContact : Integrable (fun ω => max (ErrContact ω) 0) P)
    (hFmeas : AEStronglyMeasurable F P)
    (hFnonneg : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hBnonpos : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ base + (M ω + B ω) +
        max (ErrCell ω) 0 + max (ErrContact ω) 0) :
    Integrable F P ∧
      (∫ ω, F ω ∂P) ≤
        base + (∫ ω, max (ErrCell ω) 0 ∂P) +
          (∫ ω, max (ErrContact ω) 0 ∂P) := by sorry
