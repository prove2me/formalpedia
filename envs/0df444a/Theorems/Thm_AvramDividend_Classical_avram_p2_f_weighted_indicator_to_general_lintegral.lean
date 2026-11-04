-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_indicator_to_general_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_indicator_to_general_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:06:24.633284+00:00
-- url     : https://prove2.me/theorems/086b5c5f-3e08-493a-a7e3-c71ad772100c
-- title:
--   Extend nonnegative past-event rectangle compensation to arbitrary adapted ENNReal weights
-- statement:
--   Under a smaller past measurable space mPast included in the ambient sigma-algebra, suppose the expectation of a measurable nonnegative random variable N on each mPast-measurable event A is μ(A)*r. Then for every nonnegative mPast-measurable ENNReal weight H, E[H*N]=E[H]*r, without finiteness, boundedness, independence or a specific jump-rate identity. The proof uses measurable ENNReal induction on indicator functions, disjoint finite sums and monotone increasing limits. This is the generic indicator-to-weight closure needed for source original jump compensation and predictable simple processes.
-- source:
--   Abstracts the proved event rectangle factorisation ad24b83b and W7-06 event target ea8700f6 into the adapted weight target d27347c9 and P2-E original compensator 393b03a8. Explicit event-moment hypothesis is supplied by a separate genuine source theorem, never mistaken for the original Lévy ν rate. Pinned Mathlib Measurable.ennreal_induction and lintegral indicator/add/iSup laws.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_indicator_to_general_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (mPast : MeasurableSpace Ω) (hm : mPast ≤ mΩ)
    (μ : Measure Ω) (N : Ω → ℝ≥0∞) (hN : Measurable N)
    (r : ℝ≥0∞)
    (hEvent : ∀ A : Set Ω, MeasurableSet[mPast] A →
      (∫⁻ ω in A, N ω ∂μ) = μ A * r)
    (H : Ω → ℝ≥0∞) (hH : Measurable[mPast] H) :
    (∫⁻ ω, H ω * N ω ∂μ) = (∫⁻ ω, H ω ∂μ) * r := by sorry
